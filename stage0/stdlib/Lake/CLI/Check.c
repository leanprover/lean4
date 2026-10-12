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
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl(uint8_t v_x_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_box(v_x_37_);
v___x_39_ = lean_obj_tag_nat(v___x_38_);
lean_dec(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_37_ = stack[0].m_num;
lean_object* v_res_40_;
v_res_40_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl(v_x_37_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl___boxed(lean_object* v_x_41_){
_start:
{
uint8_t v_x_4__boxed_42_; lean_object* v_res_43_; 
v_x_4__boxed_42_ = lean_unbox(v_x_41_);
v_res_43_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorIdx___impl(v_x_4__boxed_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg(lean_object* v_k_44_){
_start:
{
lean_inc(v_k_44_);
return v_k_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg___boxed(lean_object* v_k_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim___redArg(v_k_45_);
lean_dec(v_k_45_);
return v_res_46_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim(lean_object* v_motive_47_, lean_object* v_ctorIdx_48_, uint8_t v_t_49_, lean_object* v_h_50_, lean_object* v_k_51_){
_start:
{
lean_inc(v_k_51_);
return v_k_51_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_48_ = stack[1].m_obj;
uint8_t v_t_49_ = stack[2].m_num;
lean_object* v_k_51_ = stack[4].m_obj;
lean_object* v_res_52_;
v_res_52_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ctorElim(lean_box(0), v_ctorIdx_48_, v_t_49_, lean_box(0), v_k_51_);
stack->m_obj
 = v_res_52_;
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
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(lean_object* v_motive_63_, uint8_t v_t_64_, lean_object* v_h_65_, lean_object* v_check_66_){
_start:
{
lean_inc(v_check_66_);
return v_check_66_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_64_ = stack[1].m_num;
lean_object* v_check_66_ = stack[3].m_obj;
lean_object* v_res_67_;
v_res_67_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(lean_box(0), v_t_64_, lean_box(0), v_check_66_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_check_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_check_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_check_71_);
lean_dec(v_check_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg(lean_object* v_solution_74_){
_start:
{
lean_inc(v_solution_74_);
return v_solution_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg___boxed(lean_object* v_solution_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___redArg(v_solution_75_);
lean_dec(v_solution_75_);
return v_res_76_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_solution_80_){
_start:
{
lean_inc(v_solution_80_);
return v_solution_80_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_78_ = stack[1].m_num;
lean_object* v_solution_80_ = stack[3].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(lean_box(0), v_t_78_, lean_box(0), v_solution_80_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim___boxed(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_solution_85_){
_start:
{
uint8_t v_t_boxed_86_; lean_object* v_res_87_; 
v_t_boxed_86_ = lean_unbox(v_t_83_);
v_res_87_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_solution_elim(v_motive_82_, v_t_boxed_86_, v_h_84_, v_solution_85_);
lean_dec(v_solution_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg(lean_object* v_challenge_88_){
_start:
{
lean_inc(v_challenge_88_);
return v_challenge_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg___boxed(lean_object* v_challenge_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___redArg(v_challenge_89_);
lean_dec(v_challenge_89_);
return v_res_90_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(lean_object* v_motive_91_, uint8_t v_t_92_, lean_object* v_h_93_, lean_object* v_challenge_94_){
_start:
{
lean_inc(v_challenge_94_);
return v_challenge_94_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_92_ = stack[1].m_num;
lean_object* v_challenge_94_ = stack[3].m_obj;
lean_object* v_res_95_;
v_res_95_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(lean_box(0), v_t_92_, lean_box(0), v_challenge_94_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim___boxed(lean_object* v_motive_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_challenge_99_){
_start:
{
uint8_t v_t_boxed_100_; lean_object* v_res_101_; 
v_t_boxed_100_ = lean_unbox(v_t_97_);
v_res_101_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_challenge_elim(v_motive_96_, v_t_boxed_100_, v_h_98_, v_challenge_99_);
lean_dec(v_challenge_99_);
return v_res_101_;
}
}
uint8_t l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(lean_object* v_n_102_){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_nat_dec_le(v_n_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_dec_le(v_n_102_, v___x_105_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 2;
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = 1;
return v___x_108_;
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_102_ = stack[0].m_obj;
uint8_t v_res_110_;
v_res_110_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(v_n_102_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat___boxed(lean_object* v_n_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l___private_Lake_CLI_Check_0__Lake_Check_ModuleKind_ofNat(v_n_111_);
lean_dec(v_n_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint8_t l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(uint8_t v_x_114_, uint8_t v_y_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_116_ = lean_box(v_x_114_);
v___x_117_ = lean_obj_tag_nat(v___x_116_);
lean_dec(v___x_116_);
v___x_118_ = lean_box(v_y_115_);
v___x_119_ = lean_obj_tag_nat(v___x_118_);
lean_dec(v___x_118_);
v___x_120_ = lean_nat_dec_eq(v___x_117_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_114_ = stack[0].m_num;
uint8_t v_y_115_ = stack[1].m_num;
uint8_t v_res_121_;
v_res_121_ = l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(v_x_114_, v_y_115_);
stack->m_num = v_res_121_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind___boxed(lean_object* v_x_122_, lean_object* v_y_123_){
_start:
{
uint8_t v_x_23__boxed_124_; uint8_t v_y_24__boxed_125_; uint8_t v_res_126_; lean_object* v_r_127_; 
v_x_23__boxed_124_ = lean_unbox(v_x_122_);
v_y_24__boxed_125_ = lean_unbox(v_y_123_);
v_res_126_ = l___private_Lake_CLI_Check_0__Lake_Check_instDecidableEqModuleKind(v_x_23__boxed_124_, v_y_24__boxed_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = lean_nat_to_int(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(1u);
v___x_140_ = lean_nat_to_int(v___x_139_);
return v___x_140_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr(uint8_t v_x_141_, lean_object* v_prec_142_){
_start:
{
lean_object* v___y_144_; lean_object* v___y_151_; lean_object* v___y_158_; 
switch(v_x_141_)
{
case 0:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(1024u);
v___x_165_ = lean_nat_dec_le(v___x_164_, v_prec_142_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6);
v___y_144_ = v___x_166_;
goto v___jp_143_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7);
v___y_144_ = v___x_167_;
goto v___jp_143_;
}
}
case 1:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(1024u);
v___x_169_ = lean_nat_dec_le(v___x_168_, v_prec_142_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6);
v___y_151_ = v___x_170_;
goto v___jp_150_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7);
v___y_151_ = v___x_171_;
goto v___jp_150_;
}
}
default: 
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_142_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__6);
v___y_158_ = v___x_174_;
goto v___jp_157_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__7);
v___y_158_ = v___x_175_;
goto v___jp_157_;
}
}
}
v___jp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_145_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__1));
lean_inc(v___y_144_);
v___x_146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_146_, 0, v___y_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = 0;
v___x_148_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*1, v___x_147_);
v___x_149_ = l_Repr_addAppParen(v___x_148_, v_prec_142_);
return v___x_149_;
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_152_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__3));
lean_inc(v___y_151_);
v___x_153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_153_, 0, v___y_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_154_);
v___x_156_ = l_Repr_addAppParen(v___x_155_, v_prec_142_);
return v___x_156_;
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_159_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___closed__5));
lean_inc(v___y_158_);
v___x_160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_160_, 0, v___y_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = 0;
v___x_162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_161_);
v___x_163_ = l_Repr_addAppParen(v___x_162_, v_prec_142_);
return v___x_163_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_141_ = stack[0].m_num;
lean_object* v_prec_142_ = stack[1].m_obj;
lean_object* v_res_176_;
v_res_176_ = l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr(v_x_141_, v_prec_142_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr___boxed(lean_object* v_x_177_, lean_object* v_prec_178_){
_start:
{
uint8_t v_x_171__boxed_179_; lean_object* v_res_180_; 
v_x_171__boxed_179_ = lean_unbox(v_x_177_);
v_res_180_ = l___private_Lake_CLI_Check_0__Lake_Check_instReprModuleKind_repr(v_x_171__boxed_179_, v_prec_178_);
lean_dec(v_prec_178_);
return v_res_180_;
}
}
uint64_t l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(uint8_t v_x_183_){
_start:
{
switch(v_x_183_)
{
case 0:
{
uint64_t v___x_184_; 
v___x_184_ = 0ULL;
return v___x_184_;
}
case 1:
{
uint64_t v___x_185_; 
v___x_185_ = 1ULL;
return v___x_185_;
}
default: 
{
uint64_t v___x_186_; 
v___x_186_ = 2ULL;
return v___x_186_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_183_ = stack[0].m_num;
uint64_t v_res_187_;
v_res_187_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_x_183_);
stack->m_num = v_res_187_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash___boxed(lean_object* v_x_188_){
_start:
{
uint8_t v_x_40__boxed_189_; uint64_t v_res_190_; lean_object* v_r_191_; 
v_x_40__boxed_189_ = lean_unbox(v_x_188_);
v_res_190_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_x_40__boxed_189_);
v_r_191_ = lean_box_uint64(v_res_190_);
return v_r_191_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(lean_object* v_a_194_){
_start:
{
lean_object* v_externalKernels_196_; lean_object* v___x_197_; 
v_externalKernels_196_ = lean_ctor_get(v_a_194_, 15);
lean_inc(v_externalKernels_196_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_externalKernels_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_194_ = stack[0].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(v_a_194_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels___boxed(lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lake_CLI_Check_0__Lake_Check_getExternalKernels(v_a_199_);
lean_dec_ref(v_a_199_);
return v_res_201_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(lean_object* v_a_202_){
_start:
{
lean_object* v_theoremNames_204_; lean_object* v___x_205_; 
v_theoremNames_204_ = lean_ctor_get(v_a_202_, 3);
lean_inc_ref(v_theoremNames_204_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v_theoremNames_204_);
return v___x_205_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_202_ = stack[0].m_obj;
lean_object* v_res_206_;
v_res_206_ = l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(v_a_202_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames___boxed(lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lake_CLI_Check_0__Lake_Check_getTheoremNames(v_a_207_);
lean_dec_ref(v_a_207_);
return v_res_209_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(lean_object* v_a_210_){
_start:
{
lean_object* v_definitionNames_212_; lean_object* v___x_213_; 
v_definitionNames_212_ = lean_ctor_get(v_a_210_, 4);
lean_inc_ref(v_definitionNames_212_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_definitionNames_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_210_ = stack[0].m_obj;
lean_object* v_res_214_;
v_res_214_ = l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(v_a_210_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames___boxed(lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lake_CLI_Check_0__Lake_Check_getDefinitionNames(v_a_215_);
lean_dec_ref(v_a_215_);
return v_res_217_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(lean_object* v_a_218_){
_start:
{
lean_object* v_projectDir_220_; lean_object* v___x_221_; 
v_projectDir_220_ = lean_ctor_get(v_a_218_, 0);
lean_inc_ref(v_projectDir_220_);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v_projectDir_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_218_ = stack[0].m_obj;
lean_object* v_res_222_;
v_res_222_ = l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(v_a_218_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir___boxed(lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lake_CLI_Check_0__Lake_Check_getProjectDir(v_a_223_);
lean_dec_ref(v_a_223_);
return v_res_225_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(lean_object* v_a_226_){
_start:
{
lean_object* v_leanPrefix_228_; lean_object* v___x_229_; 
v_leanPrefix_228_ = lean_ctor_get(v_a_226_, 6);
lean_inc_ref(v_leanPrefix_228_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_leanPrefix_228_);
return v___x_229_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_226_ = stack[0].m_obj;
lean_object* v_res_230_;
v_res_230_ = l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(v_a_226_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix___boxed(lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lake_CLI_Check_0__Lake_Check_getLeanPrefix(v_a_231_);
lean_dec_ref(v_a_231_);
return v_res_233_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(lean_object* v_a_234_){
_start:
{
lean_object* v_lakeHome_236_; lean_object* v___x_237_; 
v_lakeHome_236_ = lean_ctor_get(v_a_234_, 11);
lean_inc_ref(v_lakeHome_236_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_lakeHome_236_);
return v___x_237_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_234_ = stack[0].m_obj;
lean_object* v_res_238_;
v_res_238_ = l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(v_a_234_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome___boxed(lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lake_CLI_Check_0__Lake_Check_getLakeHome(v_a_239_);
lean_dec_ref(v_a_239_);
return v_res_241_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(lean_object* v_a_242_){
_start:
{
lean_object* v_challengeModule_244_; lean_object* v___x_245_; 
v_challengeModule_244_ = lean_ctor_get(v_a_242_, 1);
lean_inc(v_challengeModule_244_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v_challengeModule_244_);
return v___x_245_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_242_ = stack[0].m_obj;
lean_object* v_res_246_;
v_res_246_ = l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(v_a_242_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule___boxed(lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lake_CLI_Check_0__Lake_Check_getChallengeModule(v_a_247_);
lean_dec_ref(v_a_247_);
return v_res_249_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(lean_object* v_a_250_){
_start:
{
lean_object* v_solutionModule_252_; lean_object* v___x_253_; 
v_solutionModule_252_ = lean_ctor_get(v_a_250_, 2);
lean_inc(v_solutionModule_252_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_solutionModule_252_);
return v___x_253_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_250_ = stack[0].m_obj;
lean_object* v_res_254_;
v_res_254_ = l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(v_a_250_);
stack->m_obj
 = v_res_254_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule___boxed(lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lake_CLI_Check_0__Lake_Check_getSolutionModule(v_a_255_);
lean_dec_ref(v_a_255_);
return v_res_257_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(lean_object* v_a_258_){
_start:
{
lean_object* v_legalAxioms_260_; lean_object* v___x_261_; 
v_legalAxioms_260_ = lean_ctor_get(v_a_258_, 5);
lean_inc_ref(v_legalAxioms_260_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_legalAxioms_260_);
return v___x_261_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_258_ = stack[0].m_obj;
lean_object* v_res_262_;
v_res_262_ = l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(v_a_258_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms___boxed(lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lake_CLI_Check_0__Lake_Check_getLegalAxioms(v_a_263_);
lean_dec_ref(v_a_263_);
return v_res_265_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe(lean_object* v_exe_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_273_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_274_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__1));
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_mk_empty_array_with_capacity(v___x_275_);
v___x_277_ = lean_array_push(v___x_276_, v_exe_271_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_281_ = 1;
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_283_, 0, v___x_273_);
lean_ctor_set(v___x_283_, 1, v___x_274_);
lean_ctor_set(v___x_283_, 2, v___x_277_);
lean_ctor_set(v___x_283_, 3, v___x_278_);
lean_ctor_set(v___x_283_, 4, v___x_280_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*5, v___x_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*5 + 1, v___x_282_);
v___x_284_ = l_IO_Process_output(v___x_283_, v___x_278_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_309_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_309_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint32_t v_exitCode_289_; lean_object* v_stdout_290_; uint32_t v___x_291_; uint8_t v___x_292_; 
v_exitCode_289_ = lean_ctor_get_uint32(v_a_285_, sizeof(void*)*2);
v_stdout_290_ = lean_ctor_get(v_a_285_, 0);
lean_inc_ref(v_stdout_290_);
lean_dec(v_a_285_);
v___x_291_ = 0;
v___x_292_ = lean_uint32_dec_eq(v_exitCode_289_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_294_; 
lean_dec_ref(v_stdout_290_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_278_);
v___x_294_ = v___x_287_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_278_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_296_ = lean_string_utf8_byte_size(v_stdout_290_);
v___x_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_297_, 0, v_stdout_290_);
lean_ctor_set(v___x_297_, 1, v___x_279_);
lean_ctor_set(v___x_297_, 2, v___x_296_);
v___x_298_ = l_String_Slice_trimAscii(v___x_297_);
v___x_299_ = l_String_Slice_toString(v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = lean_string_utf8_byte_size(v___x_299_);
v___x_301_ = lean_nat_dec_eq(v___x_300_, v___x_279_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_299_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_302_);
v___x_304_ = v___x_287_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_307_; 
lean_dec_ref(v___x_299_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_278_);
v___x_307_ = v___x_287_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_278_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_284_, 0);
lean_dec(v_unused_317_);
v___x_311_ = v___x_284_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_dec(v___x_284_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set_tag(v___x_311_, 0);
lean_ctor_set(v___x_311_, 0, v___x_278_);
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_278_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_whichExe_0interp(lean_interpreter_value* stack)
{
lean_object* v_exe_271_ = stack[0].m_obj;
lean_object* v_res_318_;
v_res_318_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v_exe_271_);
stack->m_obj
 = v_res_318_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_whichExe___boxed(lean_object* v_exe_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v_exe_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(lean_object* v_cmd_325_, lean_object* v_exe_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_327_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_328_ = lean_string_append(v___x_327_, v_cmd_325_);
v___x_329_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__1));
v___x_330_ = lean_string_append(v___x_328_, v___x_329_);
v___x_331_ = lean_string_append(v___x_330_, v_exe_326_);
v___x_332_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__2));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___boxed(lean_object* v_cmd_334_, lean_object* v_exe_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_334_, v_exe_335_);
lean_dec_ref(v_exe_335_);
lean_dec_ref(v_cmd_334_);
return v_res_336_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(lean_object* v_as_337_, size_t v_sz_338_, size_t v_i_339_, lean_object* v_b_340_){
_start:
{
lean_object* v_a_343_; uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_339_, v_sz_338_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v_b_340_);
return v___x_348_;
}
else
{
lean_object* v_a_349_; lean_object* v___x_350_; 
v_a_349_ = lean_array_uget_borrowed(v_as_337_, v_i_339_);
v___x_350_ = lean_io_getenv(v_a_349_);
if (lean_obj_tag(v___x_350_) == 1)
{
lean_object* v_val_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_val_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v___x_350_, 1);
lean_inc(v_a_349_);
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_a_349_);
lean_ctor_set(v___x_352_, 1, v_val_351_);
v___x_353_ = lean_array_push(v_b_340_, v___x_352_);
v_a_343_ = v___x_353_;
goto v___jp_342_;
}
else
{
lean_dec(v___x_350_);
v_a_343_ = v_b_340_;
goto v___jp_342_;
}
}
v___jp_342_:
{
size_t v___x_344_; size_t v___x_345_; 
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_add(v_i_339_, v___x_344_);
v_i_339_ = v___x_345_;
v_b_340_ = v_a_343_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_337_ = stack[0].m_obj;
size_t v_sz_338_ = stack[1].m_num;
size_t v_i_339_ = stack[2].m_num;
lean_object* v_b_340_ = stack[3].m_obj;
lean_object* v_res_354_;
v_res_354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_as_337_, v_sz_338_, v_i_339_, v_b_340_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1___boxed(lean_object* v_as_355_, lean_object* v_sz_356_, lean_object* v_i_357_, lean_object* v_b_358_, lean_object* v___y_359_){
_start:
{
size_t v_sz_boxed_360_; size_t v_i_boxed_361_; lean_object* v_res_362_; 
v_sz_boxed_360_ = lean_unbox_usize(v_sz_356_);
lean_dec(v_sz_356_);
v_i_boxed_361_ = lean_unbox_usize(v_i_357_);
lean_dec(v_i_357_);
v_res_362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_as_355_, v_sz_boxed_360_, v_i_boxed_361_, v_b_358_);
lean_dec_ref(v_as_355_);
return v_res_362_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(lean_object* v_fst_363_, lean_object* v_as_364_, size_t v_i_365_, size_t v_stop_366_, lean_object* v_b_367_){
_start:
{
lean_object* v___y_369_; uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_eq(v_i_365_, v_stop_366_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v_fst_375_; uint8_t v___x_376_; 
v___x_374_ = lean_array_uget_borrowed(v_as_364_, v_i_365_);
v_fst_375_ = lean_ctor_get(v___x_374_, 0);
v___x_376_ = lean_string_dec_eq(v_fst_375_, v_fst_363_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_inc(v___x_374_);
v___x_377_ = lean_array_push(v_b_367_, v___x_374_);
v___y_369_ = v___x_377_;
goto v___jp_368_;
}
else
{
v___y_369_ = v_b_367_;
goto v___jp_368_;
}
}
else
{
return v_b_367_;
}
v___jp_368_:
{
size_t v___x_370_; size_t v___x_371_; 
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_365_, v___x_370_);
v_i_365_ = v___x_371_;
v_b_367_ = v___y_369_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_363_ = stack[0].m_obj;
lean_object* v_as_364_ = stack[1].m_obj;
size_t v_i_365_ = stack[2].m_num;
size_t v_stop_366_ = stack[3].m_num;
lean_object* v_b_367_ = stack[4].m_obj;
lean_object* v_res_378_;
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_363_, v_as_364_, v_i_365_, v_stop_366_, v_b_367_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0___boxed(lean_object* v_fst_379_, lean_object* v_as_380_, lean_object* v_i_381_, lean_object* v_stop_382_, lean_object* v_b_383_){
_start:
{
size_t v_i_boxed_384_; size_t v_stop_boxed_385_; lean_object* v_res_386_; 
v_i_boxed_384_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_stop_boxed_385_ = lean_unbox_usize(v_stop_382_);
lean_dec(v_stop_382_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_379_, v_as_380_, v_i_boxed_384_, v_stop_boxed_385_, v_b_383_);
lean_dec_ref(v_as_380_);
lean_dec_ref(v_fst_379_);
return v_res_386_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(lean_object* v_as_389_, size_t v_sz_390_, size_t v_i_391_, lean_object* v_b_392_){
_start:
{
lean_object* v_a_395_; uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_lt(v_i_391_, v_sz_390_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_b_392_);
return v___x_400_;
}
else
{
lean_object* v_a_401_; lean_object* v_fst_402_; lean_object* v_snd_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_425_; 
v_a_401_ = lean_array_uget(v_as_389_, v_i_391_);
v_fst_402_ = lean_ctor_get(v_a_401_, 0);
v_snd_403_ = lean_ctor_get(v_a_401_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v_a_401_);
if (v_isSharedCheck_425_ == 0)
{
v___x_405_ = v_a_401_;
v_isShared_406_ = v_isSharedCheck_425_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snd_403_);
lean_inc(v_fst_402_);
lean_dec(v_a_401_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_425_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___y_408_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_b_392_);
v___x_416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0));
v___x_417_ = lean_nat_dec_lt(v___x_414_, v___x_415_);
if (v___x_417_ == 0)
{
lean_dec_ref(v_b_392_);
v___y_408_ = v___x_416_;
goto v___jp_407_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = lean_nat_dec_le(v___x_415_, v___x_415_);
if (v___x_418_ == 0)
{
if (v___x_417_ == 0)
{
lean_dec_ref(v_b_392_);
v___y_408_ = v___x_416_;
goto v___jp_407_;
}
else
{
size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v___x_419_ = ((size_t)0ULL);
v___x_420_ = lean_usize_of_nat(v___x_415_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_402_, v_b_392_, v___x_419_, v___x_420_, v___x_416_);
lean_dec_ref(v_b_392_);
v___y_408_ = v___x_421_;
goto v___jp_407_;
}
}
else
{
size_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; 
v___x_422_ = ((size_t)0ULL);
v___x_423_ = lean_usize_of_nat(v___x_415_);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__0(v_fst_402_, v_b_392_, v___x_422_, v___x_423_, v___x_416_);
lean_dec_ref(v_b_392_);
v___y_408_ = v___x_424_;
goto v___jp_407_;
}
}
v___jp_407_:
{
if (lean_obj_tag(v_snd_403_) == 1)
{
lean_object* v_val_409_; lean_object* v___x_411_; 
v_val_409_ = lean_ctor_get(v_snd_403_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v_snd_403_, 1);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v_val_409_);
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_fst_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_val_409_);
v___x_411_ = v_reuseFailAlloc_413_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; 
v___x_412_ = lean_array_push(v___y_408_, v___x_411_);
v_a_395_ = v___x_412_;
goto v___jp_394_;
}
}
else
{
lean_del_object(v___x_405_);
lean_dec(v_snd_403_);
lean_dec(v_fst_402_);
v_a_395_ = v___y_408_;
goto v___jp_394_;
}
}
}
}
v___jp_394_:
{
size_t v___x_396_; size_t v___x_397_; 
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_add(v_i_391_, v___x_396_);
v_i_391_ = v___x_397_;
v_b_392_ = v_a_395_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_389_ = stack[0].m_obj;
size_t v_sz_390_ = stack[1].m_num;
size_t v_i_391_ = stack[2].m_num;
lean_object* v_b_392_ = stack[3].m_obj;
lean_object* v_res_426_;
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_as_389_, v_sz_390_, v_i_391_, v_b_392_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___boxed(lean_object* v_as_427_, lean_object* v_sz_428_, lean_object* v_i_429_, lean_object* v_b_430_, lean_object* v___y_431_){
_start:
{
size_t v_sz_boxed_432_; size_t v_i_boxed_433_; lean_object* v_res_434_; 
v_sz_boxed_432_ = lean_unbox_usize(v_sz_428_);
lean_dec(v_sz_428_);
v_i_boxed_433_ = lean_unbox_usize(v_i_429_);
lean_dec(v_i_429_);
v_res_434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_as_427_, v_sz_boxed_432_, v_i_boxed_433_, v_b_430_);
lean_dec_ref(v_as_427_);
return v_res_434_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(lean_object* v_spawnArgs_435_){
_start:
{
lean_object* v_envPass_437_; lean_object* v_envOverride_438_; lean_object* v_env_439_; size_t v_sz_440_; size_t v___x_441_; lean_object* v___x_442_; 
v_envPass_437_ = lean_ctor_get(v_spawnArgs_435_, 2);
v_envOverride_438_ = lean_ctor_get(v_spawnArgs_435_, 3);
v_env_439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2___closed__0));
v_sz_440_ = lean_array_size(v_envPass_437_);
v___x_441_ = ((size_t)0ULL);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__1(v_envPass_437_, v_sz_440_, v___x_441_, v_env_439_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; size_t v_sz_444_; lean_object* v___x_445_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v_sz_444_ = lean_array_size(v_envOverride_438_);
v___x_445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_spec__2(v_envOverride_438_, v_sz_444_, v___x_441_, v_a_443_);
return v___x_445_;
}
else
{
return v___x_442_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_spawnArgs_435_ = stack[0].m_obj;
lean_object* v_res_446_;
v_res_446_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_435_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv___boxed(lean_object* v_spawnArgs_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_447_);
lean_dec_ref(v_spawnArgs_447_);
return v_res_449_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = lean_mk_empty_array_with_capacity(v___x_452_);
v___x_454_ = lean_array_push(v___x_453_, v___x_451_);
return v___x_454_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(lean_object* v_as_455_, size_t v_i_456_, size_t v_stop_457_, lean_object* v_b_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_eq(v_i_456_, v_stop_457_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; size_t v___x_464_; size_t v___x_465_; 
v___x_460_ = lean_array_uget_borrowed(v_as_455_, v_i_456_);
v___x_461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__1);
lean_inc(v___x_460_);
v___x_462_ = lean_array_push(v___x_461_, v___x_460_);
v___x_463_ = l_Array_append___redArg(v_b_458_, v___x_462_);
lean_dec_ref(v___x_462_);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_add(v_i_456_, v___x_464_);
v_i_456_ = v___x_465_;
v_b_458_ = v___x_463_;
goto _start;
}
else
{
return v_b_458_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_455_ = stack[0].m_obj;
size_t v_i_456_ = stack[1].m_num;
size_t v_stop_457_ = stack[2].m_num;
lean_object* v_b_458_ = stack[3].m_obj;
lean_object* v_res_467_;
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_as_455_, v_i_456_, v_stop_457_, v_b_458_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___boxed(lean_object* v_as_468_, lean_object* v_i_469_, lean_object* v_stop_470_, lean_object* v_b_471_){
_start:
{
size_t v_i_boxed_472_; size_t v_stop_boxed_473_; lean_object* v_res_474_; 
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_stop_boxed_473_ = lean_unbox_usize(v_stop_470_);
lean_dec(v_stop_470_);
v_res_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_as_468_, v_i_boxed_472_, v_stop_boxed_473_, v_b_471_);
lean_dec_ref(v_as_468_);
return v_res_474_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_477_ = lean_unsigned_to_nat(3u);
v___x_478_ = lean_mk_empty_array_with_capacity(v___x_477_);
v___x_479_ = lean_array_push(v___x_478_, v___x_476_);
return v___x_479_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(lean_object* v_as_480_, size_t v_i_481_, size_t v_stop_482_, lean_object* v_b_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_eq(v_i_481_, v_stop_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; 
v___x_485_ = lean_array_uget_borrowed(v_as_480_, v_i_481_);
v___x_486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__1);
lean_inc_n(v___x_485_, 2);
v___x_487_ = lean_array_push(v___x_486_, v___x_485_);
v___x_488_ = lean_array_push(v___x_487_, v___x_485_);
v___x_489_ = l_Array_append___redArg(v_b_483_, v___x_488_);
lean_dec_ref(v___x_488_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_481_, v___x_490_);
v_i_481_ = v___x_491_;
v_b_483_ = v___x_489_;
goto _start;
}
else
{
return v_b_483_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_480_ = stack[0].m_obj;
size_t v_i_481_ = stack[1].m_num;
size_t v_stop_482_ = stack[2].m_num;
lean_object* v_b_483_ = stack[3].m_obj;
lean_object* v_res_493_;
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_as_480_, v_i_481_, v_stop_482_, v_b_483_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___boxed(lean_object* v_as_494_, lean_object* v_i_495_, lean_object* v_stop_496_, lean_object* v_b_497_){
_start:
{
size_t v_i_boxed_498_; size_t v_stop_boxed_499_; lean_object* v_res_500_; 
v_i_boxed_498_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_stop_boxed_499_ = lean_unbox_usize(v_stop_496_);
lean_dec(v_stop_496_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_as_494_, v_i_boxed_498_, v_stop_boxed_499_, v_b_497_);
lean_dec_ref(v_as_494_);
return v_res_500_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__0));
v___x_503_ = lean_unsigned_to_nat(3u);
v___x_504_ = lean_mk_empty_array_with_capacity(v___x_503_);
v___x_505_ = lean_array_push(v___x_504_, v___x_502_);
return v___x_505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(lean_object* v_as_506_, size_t v_i_507_, size_t v_stop_508_, lean_object* v_b_509_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_eq(v_i_507_, v_stop_508_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; size_t v___x_516_; size_t v___x_517_; 
v___x_511_ = lean_array_uget_borrowed(v_as_506_, v_i_507_);
v___x_512_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___closed__1);
lean_inc_n(v___x_511_, 2);
v___x_513_ = lean_array_push(v___x_512_, v___x_511_);
v___x_514_ = lean_array_push(v___x_513_, v___x_511_);
v___x_515_ = l_Array_append___redArg(v_b_509_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_507_, v___x_516_);
v_i_507_ = v___x_517_;
v_b_509_ = v___x_515_;
goto _start;
}
else
{
return v_b_509_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_506_ = stack[0].m_obj;
size_t v_i_507_ = stack[1].m_num;
size_t v_stop_508_ = stack[2].m_num;
lean_object* v_b_509_ = stack[3].m_obj;
lean_object* v_res_519_;
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_as_506_, v_i_507_, v_stop_508_, v_b_509_);
stack->m_obj
 = v_res_519_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1___boxed(lean_object* v_as_520_, lean_object* v_i_521_, lean_object* v_stop_522_, lean_object* v_b_523_){
_start:
{
size_t v_i_boxed_524_; size_t v_stop_boxed_525_; lean_object* v_res_526_; 
v_i_boxed_524_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_stop_boxed_525_ = lean_unbox_usize(v_stop_522_);
lean_dec(v_stop_522_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_as_520_, v_i_boxed_524_, v_stop_boxed_525_, v_b_523_);
lean_dec_ref(v_as_520_);
return v_res_526_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__0));
v___x_529_ = lean_unsigned_to_nat(3u);
v___x_530_ = lean_mk_empty_array_with_capacity(v___x_529_);
v___x_531_ = lean_array_push(v___x_530_, v___x_528_);
return v___x_531_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(lean_object* v_as_532_, size_t v_i_533_, size_t v_stop_534_, lean_object* v_b_535_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = lean_usize_dec_eq(v_i_533_, v_stop_534_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v_fst_538_; lean_object* v_snd_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; 
v___x_537_ = lean_array_uget_borrowed(v_as_532_, v_i_533_);
v_fst_538_ = lean_ctor_get(v___x_537_, 0);
v_snd_539_ = lean_ctor_get(v___x_537_, 1);
v___x_540_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___closed__1);
lean_inc(v_fst_538_);
v___x_541_ = lean_array_push(v___x_540_, v_fst_538_);
lean_inc(v_snd_539_);
v___x_542_ = lean_array_push(v___x_541_, v_snd_539_);
v___x_543_ = l_Array_append___redArg(v_b_535_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_533_, v___x_544_);
v_i_533_ = v___x_545_;
v_b_535_ = v___x_543_;
goto _start;
}
else
{
return v_b_535_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_532_ = stack[0].m_obj;
size_t v_i_533_ = stack[1].m_num;
size_t v_stop_534_ = stack[2].m_num;
lean_object* v_b_535_ = stack[3].m_obj;
lean_object* v_res_547_;
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_as_532_, v_i_533_, v_stop_534_, v_b_535_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0___boxed(lean_object* v_as_548_, lean_object* v_i_549_, lean_object* v_stop_550_, lean_object* v_b_551_){
_start:
{
size_t v_i_boxed_552_; size_t v_stop_boxed_553_; lean_object* v_res_554_; 
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_stop_boxed_553_ = lean_unbox_usize(v_stop_550_);
lean_dec(v_stop_550_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_as_548_, v_i_boxed_552_, v_stop_boxed_553_, v_b_551_);
lean_dec_ref(v_as_548_);
return v_res_554_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2___closed__0));
v___x_558_ = lean_unsigned_to_nat(18u);
v___x_559_ = lean_mk_empty_array_with_capacity(v___x_558_);
v___x_560_ = lean_array_push(v___x_559_, v___x_557_);
return v___x_560_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_562_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__2);
v___x_563_ = lean_array_push(v___x_562_, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__0));
v___x_565_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__3);
v___x_566_ = lean_array_push(v___x_565_, v___x_564_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_568_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__4);
v___x_569_ = lean_array_push(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__1));
v___x_571_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__5);
v___x_572_ = lean_array_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_574_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__6);
v___x_575_ = lean_array_push(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_array_push(v___x_579_, v___x_577_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__10));
v___x_583_ = lean_unsigned_to_nat(2u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_array_push(v___x_584_, v___x_582_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__12));
v___x_588_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__7);
v___x_589_ = lean_array_push(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_591_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__13);
v___x_592_ = lean_array_push(v___x_591_, v___x_590_);
return v___x_592_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__15));
v___x_626_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__14);
v___x_627_ = lean_array_push(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3___closed__0));
v___x_629_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__31);
v___x_630_ = lean_array_push(v___x_629_, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__16));
v___x_632_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__32);
v___x_633_ = lean_array_push(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__17));
v___x_635_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__33);
v___x_636_ = lean_array_push(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__18));
v___x_638_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__34);
v___x_639_ = lean_array_push(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__26));
v___x_641_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__35);
v___x_642_ = lean_array_push(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__27));
v___x_644_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__36);
v___x_645_ = lean_array_push(v___x_644_, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__28));
v___x_647_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__37);
v___x_648_ = lean_array_push(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__29));
v___x_650_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__38);
v___x_651_ = lean_array_push(v___x_650_, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_args_654_; 
v___x_652_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__30));
v___x_653_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__39);
v_args_654_ = lean_array_push(v___x_653_, v___x_652_);
return v_args_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(lean_object* v_spawnArgs_655_, lean_object* v_env_656_, lean_object* v_projectDir_657_){
_start:
{
lean_object* v_cmd_658_; lean_object* v_args_659_; lean_object* v_readablePaths_660_; lean_object* v_writablePaths_661_; lean_object* v_tmpfsPaths_662_; uint8_t v_network_663_; lean_object* v_cwd_664_; lean_object* v___y_666_; lean_object* v___y_672_; lean_object* v___y_681_; lean_object* v_args_686_; lean_object* v___x_687_; lean_object* v___y_689_; lean_object* v___y_700_; lean_object* v___y_711_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_cmd_658_ = lean_ctor_get(v_spawnArgs_655_, 0);
lean_inc_ref(v_cmd_658_);
v_args_659_ = lean_ctor_get(v_spawnArgs_655_, 1);
lean_inc_ref(v_args_659_);
v_readablePaths_660_ = lean_ctor_get(v_spawnArgs_655_, 4);
lean_inc_ref(v_readablePaths_660_);
v_writablePaths_661_ = lean_ctor_get(v_spawnArgs_655_, 5);
lean_inc_ref(v_writablePaths_661_);
v_tmpfsPaths_662_ = lean_ctor_get(v_spawnArgs_655_, 6);
lean_inc_ref(v_tmpfsPaths_662_);
v_network_663_ = lean_ctor_get_uint8(v_spawnArgs_655_, sizeof(void*)*8);
v_cwd_664_ = lean_ctor_get(v_spawnArgs_655_, 7);
lean_inc(v_cwd_664_);
lean_dec_ref(v_spawnArgs_655_);
v_args_686_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__40);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_array_get_size(v_tmpfsPaths_662_);
v___x_722_ = lean_nat_dec_lt(v___x_687_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec_ref(v_tmpfsPaths_662_);
v___y_711_ = v_args_686_;
goto v___jp_710_;
}
else
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_le(v___x_721_, v___x_721_);
if (v___x_723_ == 0)
{
if (v___x_722_ == 0)
{
lean_dec_ref(v_tmpfsPaths_662_);
v___y_711_ = v_args_686_;
goto v___jp_710_;
}
else
{
size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; 
v___x_724_ = ((size_t)0ULL);
v___x_725_ = lean_usize_of_nat(v___x_721_);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_tmpfsPaths_662_, v___x_724_, v___x_725_, v_args_686_);
lean_dec_ref(v_tmpfsPaths_662_);
v___y_711_ = v___x_726_;
goto v___jp_710_;
}
}
else
{
size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((size_t)0ULL);
v___x_728_ = lean_usize_of_nat(v___x_721_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__3(v_tmpfsPaths_662_, v___x_727_, v___x_728_, v_args_686_);
lean_dec_ref(v_tmpfsPaths_662_);
v___y_711_ = v___x_729_;
goto v___jp_710_;
}
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_667_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__9);
v___x_668_ = lean_array_push(v___x_667_, v_cmd_658_);
v___x_669_ = l_Array_append___redArg(v___y_666_, v___x_668_);
lean_dec_ref(v___x_668_);
v___x_670_ = l_Array_append___redArg(v___x_669_, v_args_659_);
lean_dec_ref(v_args_659_);
return v___x_670_;
}
v___jp_671_:
{
if (lean_obj_tag(v_cwd_664_) == 1)
{
lean_object* v_val_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_projectDir_657_);
v_val_673_ = lean_ctor_get(v_cwd_664_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v_cwd_664_, 1);
v___x_674_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_675_ = lean_array_push(v___x_674_, v_val_673_);
v___x_676_ = l_Array_append___redArg(v___y_672_, v___x_675_);
lean_dec_ref(v___x_675_);
v___y_666_ = v___x_676_;
goto v___jp_665_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v_cwd_664_);
v___x_677_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__11);
v___x_678_ = lean_array_push(v___x_677_, v_projectDir_657_);
v___x_679_ = l_Array_append___redArg(v___y_672_, v___x_678_);
lean_dec_ref(v___x_678_);
v___y_666_ = v___x_679_;
goto v___jp_665_;
}
}
v___jp_680_:
{
lean_object* v___x_682_; lean_object* v_args_683_; 
v___x_682_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__23));
v_args_683_ = l_Array_append___redArg(v___y_681_, v___x_682_);
if (v_network_663_ == 0)
{
v___y_672_ = v_args_683_;
goto v___jp_671_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__25));
v___x_685_ = l_Array_append___redArg(v_args_683_, v___x_684_);
v___y_672_ = v___x_685_;
goto v___jp_671_;
}
}
v___jp_688_:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_array_get_size(v_env_656_);
v___x_691_ = lean_nat_dec_lt(v___x_687_, v___x_690_);
if (v___x_691_ == 0)
{
v___y_681_ = v___y_689_;
goto v___jp_680_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = lean_nat_dec_le(v___x_690_, v___x_690_);
if (v___x_692_ == 0)
{
if (v___x_691_ == 0)
{
v___y_681_ = v___y_689_;
goto v___jp_680_;
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_690_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_env_656_, v___x_693_, v___x_694_, v___y_689_);
v___y_681_ = v___x_695_;
goto v___jp_680_;
}
}
else
{
size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((size_t)0ULL);
v___x_697_ = lean_usize_of_nat(v___x_690_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__0(v_env_656_, v___x_696_, v___x_697_, v___y_689_);
v___y_681_ = v___x_698_;
goto v___jp_680_;
}
}
}
v___jp_699_:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_array_get_size(v_writablePaths_661_);
v___x_702_ = lean_nat_dec_lt(v___x_687_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec_ref(v_writablePaths_661_);
v___y_689_ = v___y_700_;
goto v___jp_688_;
}
else
{
uint8_t v___x_703_; 
v___x_703_ = lean_nat_dec_le(v___x_701_, v___x_701_);
if (v___x_703_ == 0)
{
if (v___x_702_ == 0)
{
lean_dec_ref(v_writablePaths_661_);
v___y_689_ = v___y_700_;
goto v___jp_688_;
}
else
{
size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((size_t)0ULL);
v___x_705_ = lean_usize_of_nat(v___x_701_);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_writablePaths_661_, v___x_704_, v___x_705_, v___y_700_);
lean_dec_ref(v_writablePaths_661_);
v___y_689_ = v___x_706_;
goto v___jp_688_;
}
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_707_ = ((size_t)0ULL);
v___x_708_ = lean_usize_of_nat(v___x_701_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__1(v_writablePaths_661_, v___x_707_, v___x_708_, v___y_700_);
lean_dec_ref(v_writablePaths_661_);
v___y_689_ = v___x_709_;
goto v___jp_688_;
}
}
}
v___jp_710_:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_readablePaths_660_);
v___x_713_ = lean_nat_dec_lt(v___x_687_, v___x_712_);
if (v___x_713_ == 0)
{
lean_dec_ref(v_readablePaths_660_);
v___y_700_ = v___y_711_;
goto v___jp_699_;
}
else
{
uint8_t v___x_714_; 
v___x_714_ = lean_nat_dec_le(v___x_712_, v___x_712_);
if (v___x_714_ == 0)
{
if (v___x_713_ == 0)
{
lean_dec_ref(v_readablePaths_660_);
v___y_700_ = v___y_711_;
goto v___jp_699_;
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_712_);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_readablePaths_660_, v___x_715_, v___x_716_, v___y_711_);
lean_dec_ref(v_readablePaths_660_);
v___y_700_ = v___x_717_;
goto v___jp_699_;
}
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_712_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs_spec__2(v_readablePaths_660_, v___x_718_, v___x_719_, v___y_711_);
lean_dec_ref(v_readablePaths_660_);
v___y_700_ = v___x_720_;
goto v___jp_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___boxed(lean_object* v_spawnArgs_730_, lean_object* v_env_731_, lean_object* v_projectDir_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_730_, v_env_731_, v_projectDir_732_);
lean_dec_ref(v_env_731_);
return v_res_733_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_735_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__0));
v___x_736_ = lean_unsigned_to_nat(2u);
v___x_737_ = lean_mk_empty_array_with_capacity(v___x_736_);
v___x_738_ = lean_array_push(v___x_737_, v___x_735_);
return v___x_738_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(lean_object* v_spawnArgs_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_whichSandbox_742_; 
v_whichSandbox_742_ = lean_ctor_get(v_a_740_, 9);
if (lean_obj_tag(v_whichSandbox_742_) == 0)
{
lean_object* v_projectDir_743_; lean_object* v___x_744_; lean_object* v_cmd_745_; lean_object* v_args_746_; lean_object* v_envOverride_747_; lean_object* v_cwd_748_; lean_object* v___y_750_; 
v_projectDir_743_ = lean_ctor_get(v_a_740_, 0);
v___x_744_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v_cmd_745_ = lean_ctor_get(v_spawnArgs_739_, 0);
lean_inc_ref(v_cmd_745_);
v_args_746_ = lean_ctor_get(v_spawnArgs_739_, 1);
lean_inc_ref(v_args_746_);
v_envOverride_747_ = lean_ctor_get(v_spawnArgs_739_, 3);
lean_inc_ref(v_envOverride_747_);
v_cwd_748_ = lean_ctor_get(v_spawnArgs_739_, 7);
lean_inc(v_cwd_748_);
lean_dec_ref(v_spawnArgs_739_);
if (lean_obj_tag(v_cwd_748_) == 1)
{
v___y_750_ = v_cwd_748_;
goto v___jp_749_;
}
else
{
lean_object* v___x_755_; 
lean_dec(v_cwd_748_);
lean_inc_ref(v_projectDir_743_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_projectDir_743_);
v___y_750_ = v___x_755_;
goto v___jp_749_;
}
v___jp_749_:
{
uint8_t v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_751_ = 1;
v___x_752_ = 0;
v___x_753_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_753_, 0, v___x_744_);
lean_ctor_set(v___x_753_, 1, v_cmd_745_);
lean_ctor_set(v___x_753_, 2, v_args_746_);
lean_ctor_set(v___x_753_, 3, v___y_750_);
lean_ctor_set(v___x_753_, 4, v_envOverride_747_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*5, v___x_751_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*5 + 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
else
{
lean_object* v_projectDir_756_; lean_object* v_whichEnvBin_757_; lean_object* v_path_758_; lean_object* v___x_759_; 
v_projectDir_756_ = lean_ctor_get(v_a_740_, 0);
v_whichEnvBin_757_ = lean_ctor_get(v_a_740_, 14);
v_path_758_ = lean_ctor_get(v_whichSandbox_742_, 0);
v___x_759_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxEnv(v_spawnArgs_739_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_777_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_777_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_777_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_777_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_764_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_765_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___closed__1);
lean_inc_ref(v_path_758_);
v___x_766_ = lean_array_push(v___x_765_, v_path_758_);
lean_inc_ref_n(v_projectDir_756_, 2);
v___x_767_ = l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs(v_spawnArgs_739_, v_a_760_, v_projectDir_756_);
lean_dec(v_a_760_);
v___x_768_ = l_Array_append___redArg(v___x_766_, v___x_767_);
lean_dec_ref(v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_projectDir_756_);
v___x_770_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__2));
v___x_771_ = 1;
v___x_772_ = 0;
lean_inc_ref(v_whichEnvBin_757_);
v___x_773_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_773_, 0, v___x_764_);
lean_ctor_set(v___x_773_, 1, v_whichEnvBin_757_);
lean_ctor_set(v___x_773_, 2, v___x_768_);
lean_ctor_set(v___x_773_, 3, v___x_769_);
lean_ctor_set(v___x_773_, 4, v___x_770_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*5, v___x_771_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*5 + 1, v___x_772_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_773_);
v___x_775_ = v___x_762_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_spawnArgs_739_);
v_a_778_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_759_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_759_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_spawnArgs_739_ = stack[0].m_obj;
lean_object* v_a_740_ = stack[1].m_obj;
lean_object* v_res_786_;
v_res_786_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_739_, v_a_740_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs___boxed(lean_object* v_spawnArgs_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_787_, v_a_788_);
lean_dec_ref(v_a_788_);
return v_res_790_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(lean_object* v_handle_791_, lean_object* v_child_792_){
_start:
{
lean_object* v_stdout_794_; size_t v___x_795_; lean_object* v___x_796_; 
v_stdout_794_ = lean_ctor_get(v_child_792_, 1);
v___x_795_ = ((size_t)4096ULL);
v___x_796_ = lean_io_prim_handle_read(v_stdout_794_, v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; uint8_t v___x_798_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_ByteArray_isEmpty(v_a_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = lean_io_prim_handle_write(v_handle_791_, v_a_797_);
lean_dec(v_a_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_dec_ref_known(v___x_799_, 1);
goto _start;
}
else
{
return v___x_799_;
}
}
else
{
lean_object* v___x_801_; 
lean_dec(v_a_797_);
v___x_801_ = lean_io_prim_handle_flush(v_handle_791_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v___x_801_, 0);
lean_dec(v_unused_810_);
v___x_803_ = v___x_801_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_dec(v___x_801_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = lean_box(0);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
return v___x_801_;
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_796_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_796_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_handle_791_ = stack[0].m_obj;
lean_object* v_child_792_ = stack[1].m_obj;
lean_object* v_res_819_;
v_res_819_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_791_, v_child_792_);
stack->m_obj
 = v_res_819_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg___boxed(lean_object* v_handle_820_, lean_object* v_child_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_820_, v_child_821_);
lean_dec_ref(v_child_821_);
lean_dec(v_handle_820_);
return v_res_823_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(lean_object* v_handle_824_, lean_object* v_args_825_, lean_object* v_child_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_824_, v_child_826_);
return v___x_828_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_handle_824_ = stack[0].m_obj;
lean_object* v_args_825_ = stack[1].m_obj;
lean_object* v_child_826_ = stack[2].m_obj;
lean_object* v_res_829_;
v_res_829_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(v_handle_824_, v_args_825_, v_child_826_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___boxed(lean_object* v_handle_830_, lean_object* v_args_831_, lean_object* v_child_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop(v_handle_830_, v_args_831_, v_child_832_);
lean_dec_ref(v_child_832_);
lean_dec_ref(v_args_831_);
lean_dec(v_handle_830_);
return v_res_834_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(lean_object* v_e_835_){
_start:
{
if (lean_obj_tag(v_e_835_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_846_; 
v_a_837_ = lean_ctor_get(v_e_835_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_e_835_);
if (v_isSharedCheck_846_ == 0)
{
v___x_839_ = v_e_835_;
v_isShared_840_ = v_isSharedCheck_846_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v_e_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_846_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = lean_io_error_to_string(v_a_837_);
v___x_842_ = lean_mk_io_user_error(v___x_841_);
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 1);
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v_e_835_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_e_835_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v_e_835_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v_e_835_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 0);
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_835_ = stack[0].m_obj;
lean_object* v_res_855_;
v_res_855_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_835_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg___boxed(lean_object* v_e_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_856_);
return v_res_858_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(lean_object* v_00_u03b1_859_, lean_object* v_e_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v_e_860_);
return v___x_862_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_860_ = stack[1].m_obj;
lean_object* v_res_863_;
v_res_863_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(lean_box(0), v_e_860_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___boxed(lean_object* v_00_u03b1_864_, lean_object* v_e_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0(v_00_u03b1_864_, v_e_865_);
return v_res_867_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(lean_object* v_handle_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_loop___redArg(v_handle_868_, v_a_869_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 1);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_871_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_871_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set_tag(v___x_882_, 0);
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_handle_868_ = stack[0].m_obj;
lean_object* v_a_869_ = stack[1].m_obj;
lean_object* v_res_888_;
v_res_888_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(v_handle_868_, v_a_869_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed(lean_object* v_handle_889_, lean_object* v_a_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0(v_handle_889_, v_a_890_);
lean_dec_ref(v_a_890_);
lean_dec(v_handle_889_);
return v_res_892_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(lean_object* v_handle_896_, lean_object* v_args_897_){
_start:
{
lean_object* v___x_899_; lean_object* v_cmd_900_; lean_object* v_args_901_; lean_object* v_cwd_902_; lean_object* v_env_903_; uint8_t v_inheritEnv_904_; uint8_t v_setsid_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_965_; 
v___x_899_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___closed__0));
v_cmd_900_ = lean_ctor_get(v_args_897_, 1);
v_args_901_ = lean_ctor_get(v_args_897_, 2);
v_cwd_902_ = lean_ctor_get(v_args_897_, 3);
v_env_903_ = lean_ctor_get(v_args_897_, 4);
v_inheritEnv_904_ = lean_ctor_get_uint8(v_args_897_, sizeof(void*)*5);
v_setsid_905_ = lean_ctor_get_uint8(v_args_897_, sizeof(void*)*5 + 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_args_897_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_args_897_, 0);
lean_dec(v_unused_966_);
v___x_907_ = v_args_897_;
v_isShared_908_ = v_isSharedCheck_965_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_env_903_);
lean_inc(v_cwd_902_);
lean_inc(v_args_901_);
lean_inc(v_cmd_900_);
lean_dec(v_args_897_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_965_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_899_);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_cmd_900_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_args_901_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_cwd_902_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v_env_903_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*5, v_inheritEnv_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*5 + 1, v_setsid_905_);
v___x_910_ = v_reuseFailAlloc_964_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; 
v___x_911_ = lean_io_process_spawn(v___x_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_stderr_916_; lean_object* v___x_917_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_n(v_a_912_, 2);
lean_dec_ref_known(v___x_911_, 1);
v___f_913_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___lam__0___boxed), 3, 2);
lean_closure_set(v___f_913_, 0, v_handle_896_);
lean_closure_set(v___f_913_, 1, v_a_912_);
v___x_914_ = lean_unsigned_to_nat(9u);
v___x_915_ = lean_io_as_task(v___f_913_, v___x_914_);
v_stderr_916_ = lean_ctor_get(v_a_912_, 2);
v___x_917_ = l_IO_FS_Handle_readToEnd(v_stderr_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = lean_io_process_child_wait(v___x_899_, v_a_912_);
lean_dec(v_a_912_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_939_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_939_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_939_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_939_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_task_get_own(v___x_915_);
v___x_930_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_spec__0___redArg(v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_dec_ref_known(v___x_930_, 1);
goto v___jp_924_;
}
else
{
if (lean_obj_tag(v___x_930_) == 0)
{
lean_dec_ref_known(v___x_930_, 1);
goto v___jp_924_;
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_del_object(v___x_922_);
lean_dec(v_a_920_);
lean_dec(v_a_918_);
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
v___jp_924_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_a_918_);
lean_ctor_set(v___x_925_, 1, v_a_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_925_);
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v_a_918_);
lean_dec_ref(v___x_915_);
v_a_940_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_919_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_919_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___x_915_);
lean_dec(v_a_912_);
v_a_948_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_917_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_917_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_handle_896_);
v_a_956_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_911_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_911_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput_0interp(lean_interpreter_value* stack)
{
lean_object* v_handle_896_ = stack[0].m_obj;
lean_object* v_args_897_ = stack[1].m_obj;
lean_object* v_res_967_;
v_res_967_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_896_, v_args_897_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput___boxed(lean_object* v_handle_968_, lean_object* v_args_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_968_, v_args_969_);
return v_res_971_;
}
}
lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(lean_object* v_s_972_){
_start:
{
lean_object* v___x_974_; lean_object* v_putStr_975_; lean_object* v___x_976_; 
v___x_974_ = lean_get_stderr();
v_putStr_975_ = lean_ctor_get(v___x_974_, 4);
lean_inc_ref(v_putStr_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = lean_apply_2(v_putStr_975_, v_s_972_, lean_box(0));
return v___x_976_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_972_ = stack[0].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_s_972_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0___boxed(lean_object* v_s_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_s_978_);
return v_res_980_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(lean_object* v_handle_982_, lean_object* v_spawnArgs_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_983_, v_a_984_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_pipedOutput(v_handle_982_, v_a_987_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_992_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v_fst_990_ = lean_ctor_get(v_a_989_, 0);
lean_inc(v_fst_990_);
v_snd_991_ = lean_ctor_get(v_a_989_, 1);
lean_inc(v_snd_991_);
lean_dec(v_a_989_);
v___x_992_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_fst_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_992_, 0);
lean_dec(v_unused_1013_);
v___x_994_ = v___x_992_;
v_isShared_995_ = v_isSharedCheck_1012_;
goto v_resetjp_993_;
}
else
{
lean_dec(v___x_992_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1012_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
uint32_t v___x_996_; uint32_t v___x_997_; uint8_t v___x_998_; 
v___x_996_ = 0;
v___x_997_ = lean_unbox_uint32(v_snd_991_);
v___x_998_ = lean_uint32_dec_eq(v___x_997_, v___x_996_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; uint32_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_999_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_1000_ = lean_unbox_uint32(v_snd_991_);
lean_dec(v_snd_991_);
v___x_1001_ = lean_uint32_to_nat(v___x_1000_);
v___x_1002_ = l_Nat_reprFast(v___x_1001_);
v___x_1003_ = lean_string_append(v___x_999_, v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
if (v_isShared_995_ == 0)
{
lean_ctor_set_tag(v___x_994_, 1);
lean_ctor_set(v___x_994_, 0, v___x_1004_);
v___x_1006_ = v___x_994_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_dec(v_snd_991_);
v___x_1008_ = lean_box(0);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1008_);
v___x_1010_ = v___x_994_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_dec(v_snd_991_);
return v___x_992_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_988_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_988_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_handle_982_);
v_a_1022_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_986_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_986_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_0interp(lean_interpreter_value* stack)
{
lean_object* v_handle_982_ = stack[0].m_obj;
lean_object* v_spawnArgs_983_ = stack[1].m_obj;
lean_object* v_a_984_ = stack[2].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_982_, v_spawnArgs_983_, v_a_984_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___boxed(lean_object* v_handle_1031_, lean_object* v_spawnArgs_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_1031_, v_spawnArgs_1032_, v_a_1033_);
lean_dec_ref(v_a_1033_);
return v_res_1035_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(lean_object* v_spawnArgs_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1041_ = lean_box(0);
v___x_1042_ = l_IO_Process_output(v_a_1040_, v___x_1041_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; uint32_t v_exitCode_1044_; lean_object* v_stdout_1045_; lean_object* v_stderr_1046_; lean_object* v___x_1047_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_exitCode_1044_ = lean_ctor_get_uint32(v_a_1043_, sizeof(void*)*2);
v_stdout_1045_ = lean_ctor_get(v_a_1043_, 0);
lean_inc_ref(v_stdout_1045_);
v_stderr_1046_ = lean_ctor_get(v_a_1043_, 1);
lean_inc_ref(v_stderr_1046_);
lean_dec(v_a_1043_);
v___x_1047_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v_stderr_1046_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1064_; 
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1047_, 0);
lean_dec(v_unused_1065_);
v___x_1049_ = v___x_1047_;
v_isShared_1050_ = v_isSharedCheck_1064_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v___x_1047_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1064_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
uint32_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 0;
v___x_1052_ = lean_uint32_dec_eq(v_exitCode_1044_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec_ref(v_stdout_1045_);
v___x_1053_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_1054_ = lean_uint32_to_nat(v_exitCode_1044_);
v___x_1055_ = l_Nat_reprFast(v___x_1054_);
v___x_1056_ = lean_string_append(v___x_1053_, v___x_1055_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1057_);
v___x_1059_ = v___x_1049_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
lean_object* v___x_1062_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v_stdout_1045_);
v___x_1062_ = v___x_1049_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_stdout_1045_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_stdout_1045_);
v_a_1066_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1047_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1047_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_a_1074_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1042_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1042_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1039_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1039_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout_0interp(lean_interpreter_value* stack)
{
lean_object* v_spawnArgs_1036_ = stack[0].m_obj;
lean_object* v_a_1037_ = stack[1].m_obj;
lean_object* v_res_1090_;
v_res_1090_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v_spawnArgs_1036_, v_a_1037_);
stack->m_obj
 = v_res_1090_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout___boxed(lean_object* v_spawnArgs_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v_spawnArgs_1091_, v_a_1092_);
lean_dec_ref(v_a_1092_);
return v_res_1094_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(lean_object* v_spawnArgs_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l___private_Lake_CLI_Check_0__Lake_Check_sandboxSpawnArgs(v_spawnArgs_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = lean_io_process_spawn(v_a_1099_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_whichExe___closed__0));
v___x_1103_ = lean_io_process_child_wait(v___x_1102_, v_a_1101_);
lean_dec(v_a_1101_);
return v___x_1103_;
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1100_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1100_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
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
v_a_1112_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1098_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1098_);
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
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_spawnArgs_1095_ = stack[0].m_obj;
lean_object* v_a_1096_ = stack[1].m_obj;
lean_object* v_res_1120_;
v_res_1120_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_1095_, v_a_1096_);
stack->m_obj
 = v_res_1120_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode___boxed(lean_object* v_spawnArgs_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_1121_, v_a_1122_);
lean_dec_ref(v_a_1122_);
return v_res_1124_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(lean_object* v_spawnArgs_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v_spawnArgs_1125_, v_a_1126_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1149_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1149_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
uint32_t v___x_1133_; uint32_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1133_ = 0;
v___x_1134_ = lean_unbox_uint32(v_a_1129_);
v___x_1135_ = lean_uint32_dec_eq(v___x_1134_, v___x_1133_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; uint32_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1136_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo___closed__0));
v___x_1137_ = lean_unbox_uint32(v_a_1129_);
lean_dec(v_a_1129_);
v___x_1138_ = lean_uint32_to_nat(v___x_1137_);
v___x_1139_ = l_Nat_reprFast(v___x_1138_);
v___x_1140_ = lean_string_append(v___x_1136_, v___x_1139_);
lean_dec_ref(v___x_1139_);
v___x_1141_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 1);
lean_ctor_set(v___x_1131_, 0, v___x_1141_);
v___x_1143_ = v___x_1131_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_a_1129_);
v___x_1145_ = lean_box(0);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1145_);
v___x_1147_ = v___x_1131_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1128_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1128_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed_0interp(lean_interpreter_value* stack)
{
lean_object* v_spawnArgs_1125_ = stack[0].m_obj;
lean_object* v_a_1126_ = stack[1].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v_spawnArgs_1125_, v_a_1126_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed___boxed(lean_object* v_spawnArgs_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v_spawnArgs_1159_, v_a_1160_);
lean_dec_ref(v_a_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(lean_object* v_s_1164_){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_string_utf8_byte_size(v_s_1164_);
v___x_1166_ = lean_unsigned_to_nat(10u);
v___x_1167_ = lean_nat_dec_le(v___x_1166_, v___x_1165_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
lean_dec_ref(v_s_1164_);
v___x_1168_ = lean_box(0);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1169_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg___closed__0));
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_string_memcmp(v_s_1164_, v___x_1169_, v___x_1170_, v___x_1170_, v___x_1166_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_dec_ref(v_s_1164_);
v___x_1172_ = lean_box(0);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_inc_ref(v_s_1164_);
v___x_1173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1173_, 0, v_s_1164_);
lean_ctor_set(v___x_1173_, 1, v___x_1170_);
lean_ctor_set(v___x_1173_, 2, v___x_1165_);
v___x_1174_ = l_String_Slice_pos_x21(v___x_1173_, v___x_1166_);
lean_dec_ref_known(v___x_1173_, 3);
v___x_1175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1175_, 0, v_s_1164_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
lean_ctor_set(v___x_1175_, 2, v___x_1165_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(lean_object* v_s_1177_, lean_object* v_pat_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_s_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___boxed(lean_object* v_s_1180_, lean_object* v_pat_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0(v_s_1180_, v_pat_1181_);
lean_dec_ref(v_pat_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(lean_object* v_s_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = lean_string_utf8_byte_size(v_s_1184_);
v___x_1186_ = lean_unsigned_to_nat(5u);
v___x_1187_ = lean_nat_dec_le(v___x_1186_, v___x_1185_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_dec_ref(v_s_1184_);
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg___closed__0));
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_string_memcmp(v_s_1184_, v___x_1189_, v___x_1190_, v___x_1190_, v___x_1186_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; 
lean_dec_ref(v_s_1184_);
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_inc_ref(v_s_1184_);
v___x_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1193_, 0, v_s_1184_);
lean_ctor_set(v___x_1193_, 1, v___x_1190_);
lean_ctor_set(v___x_1193_, 2, v___x_1185_);
v___x_1194_ = l_String_Slice_pos_x21(v___x_1193_, v___x_1186_);
lean_dec_ref_known(v___x_1193_, 3);
v___x_1195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_s_1184_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
lean_ctor_set(v___x_1195_, 2, v___x_1185_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(lean_object* v_s_1197_, lean_object* v_pat_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_s_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___boxed(lean_object* v_s_1200_, lean_object* v_pat_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1(v_s_1200_, v_pat_1201_);
lean_dec_ref(v_pat_1201_);
return v_res_1202_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg(){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___closed__0));
return v___x_1206_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1207_;
v_res_1207_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg___boxed(lean_object* v___dummy_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v_res_1209_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___redArg();
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(lean_object* v_s_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___boxed(lean_object* v_s_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3(v_s_1213_);
lean_dec_ref(v_s_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(lean_object* v_a_1215_, lean_object* v___x_1216_, lean_object* v___x_1217_, lean_object* v_a_1218_, lean_object* v_b_1219_){
_start:
{
lean_object* v_it_1221_; lean_object* v_startInclusive_1222_; lean_object* v_endExclusive_1223_; 
if (lean_obj_tag(v_a_1218_) == 0)
{
lean_object* v_currPos_1228_; lean_object* v_searcher_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1252_; 
v_currPos_1228_ = lean_ctor_get(v_a_1218_, 0);
v_searcher_1229_ = lean_ctor_get(v_a_1218_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_a_1218_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1231_ = v_a_1218_;
v_isShared_1232_ = v_isSharedCheck_1252_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_searcher_1229_);
lean_inc(v_currPos_1228_);
lean_dec(v_a_1218_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1252_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
uint8_t v_decide_1233_; 
v_decide_1233_ = lean_nat_dec_eq(v_searcher_1229_, v___x_1217_);
if (v_decide_1233_ == 0)
{
uint32_t v___x_1234_; uint32_t v___x_1235_; uint8_t v___x_1236_; 
v___x_1234_ = 10;
v___x_1235_ = lean_string_utf8_get_fast(v_a_1215_, v_searcher_1229_);
v___x_1236_ = lean_uint32_dec_eq(v___x_1235_, v___x_1234_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_string_utf8_next_fast(v_a_1215_, v_searcher_1229_);
lean_dec(v_searcher_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1237_);
v___x_1239_ = v___x_1231_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_currPos_1228_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
v_a_1218_ = v___x_1239_;
goto _start;
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_slice_1245_; lean_object* v_nextIt_1247_; 
v___x_1242_ = lean_string_utf8_next_fast(v_a_1215_, v_searcher_1229_);
v___x_1243_ = lean_nat_sub(v___x_1242_, v_searcher_1229_);
v___x_1244_ = lean_nat_add(v_searcher_1229_, v___x_1243_);
lean_dec(v___x_1243_);
v_slice_1245_ = l_String_Slice_subslice_x21(v___x_1216_, v_currPos_1228_, v_searcher_1229_);
lean_inc(v___x_1244_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1244_);
lean_ctor_set(v___x_1231_, 0, v___x_1244_);
v_nextIt_1247_ = v___x_1231_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1244_);
v_nextIt_1247_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v_startInclusive_1248_; lean_object* v_endExclusive_1249_; 
v_startInclusive_1248_ = lean_ctor_get(v_slice_1245_, 0);
lean_inc(v_startInclusive_1248_);
v_endExclusive_1249_ = lean_ctor_get(v_slice_1245_, 1);
lean_inc(v_endExclusive_1249_);
lean_dec_ref(v_slice_1245_);
v_it_1221_ = v_nextIt_1247_;
v_startInclusive_1222_ = v_startInclusive_1248_;
v_endExclusive_1223_ = v_endExclusive_1249_;
goto v___jp_1220_;
}
}
}
else
{
lean_object* v___x_1251_; 
lean_del_object(v___x_1231_);
lean_dec(v_searcher_1229_);
v___x_1251_ = lean_box(1);
lean_inc(v___x_1217_);
v_it_1221_ = v___x_1251_;
v_startInclusive_1222_ = v_currPos_1228_;
v_endExclusive_1223_ = v___x_1217_;
goto v___jp_1220_;
}
}
}
else
{
lean_dec(v___x_1217_);
lean_dec_ref(v_a_1215_);
return v_b_1219_;
}
v___jp_1220_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_inc_ref(v_a_1215_);
v___x_1224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1215_);
lean_ctor_set(v___x_1224_, 1, v_startInclusive_1222_);
lean_ctor_set(v___x_1224_, 2, v_endExclusive_1223_);
v___x_1225_ = l_String_Slice_toString(v___x_1224_);
lean_dec_ref_known(v___x_1224_, 3);
v___x_1226_ = lean_array_push(v_b_1219_, v___x_1225_);
v_a_1218_ = v_it_1221_;
v_b_1219_ = v___x_1226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg___boxed(lean_object* v_a_1253_, lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v_a_1256_, lean_object* v_b_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1253_, v___x_1254_, v___x_1255_, v_a_1256_, v_b_1257_);
lean_dec_ref(v___x_1254_);
return v_res_1258_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(lean_object* v_as_x27_1259_, lean_object* v_b_1260_){
_start:
{
if (lean_obj_tag(v_as_x27_1259_) == 0)
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_b_1260_);
return v___x_1262_;
}
else
{
lean_object* v_head_1263_; lean_object* v_tail_1264_; lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1288_; 
v_head_1263_ = lean_ctor_get(v_as_x27_1259_, 0);
v_tail_1264_ = lean_ctor_get(v_as_x27_1259_, 1);
v_fst_1265_ = lean_ctor_get(v_b_1260_, 0);
v_snd_1266_ = lean_ctor_get(v_b_1260_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_b_1260_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1268_ = v_b_1260_;
v_isShared_1269_ = v_isSharedCheck_1288_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v_b_1260_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1288_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; 
lean_inc(v_head_1263_);
v___x_1270_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__0___redArg(v_head_1263_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_dec(v_fst_1265_);
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = l_String_Slice_toString(v_val_1271_);
lean_dec(v_val_1271_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1272_);
v___x_1274_ = v___x_1268_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_snd_1266_);
v___x_1274_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v_as_x27_1259_ = v_tail_1264_;
v_b_1260_ = v___x_1274_;
goto _start;
}
}
else
{
lean_object* v___x_1277_; 
lean_dec(v___x_1270_);
lean_inc(v_head_1263_);
v___x_1277_ = l_String_dropPrefix_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__1___redArg(v_head_1263_);
if (lean_obj_tag(v___x_1277_) == 1)
{
lean_object* v_val_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_dec(v_snd_1266_);
v_val_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = l_String_Slice_toString(v_val_1278_);
lean_dec(v_val_1278_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1279_);
v___x_1281_ = v___x_1268_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_fst_1265_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v_as_x27_1259_ = v_tail_1264_;
v_b_1260_ = v___x_1281_;
goto _start;
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v___x_1277_);
if (v_isShared_1269_ == 0)
{
v___x_1285_ = v___x_1268_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_fst_1265_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_snd_1266_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
v_as_x27_1259_ = v_tail_1264_;
v_b_1260_ = v___x_1285_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1259_ = stack[0].m_obj;
lean_object* v_b_1260_ = stack[1].m_obj;
lean_object* v_res_1289_;
v_res_1289_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1259_, v_b_1260_);
stack->m_obj
 = v_res_1289_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg___boxed(lean_object* v_as_x27_1290_, lean_object* v_b_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1290_, v_b_1291_);
lean_dec(v_as_x27_1290_);
return v_res_1293_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(lean_object* v_s_1294_){
_start:
{
lean_object* v___x_1296_; lean_object* v_putStr_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_get_stdout();
v_putStr_1297_ = lean_ctor_get(v___x_1296_, 4);
lean_inc_ref(v_putStr_1297_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = lean_apply_2(v_putStr_1297_, v_s_1294_, lean_box(0));
return v___x_1298_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1294_ = stack[0].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_1294_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2___boxed(lean_object* v_s_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v_s_1300_);
return v_res_1302_;
}
}
lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(lean_object* v_s_1303_){
_start:
{
uint32_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = 10;
v___x_1306_ = lean_string_push(v_s_1303_, v___x_1305_);
v___x_1307_ = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_spec__2(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1303_ = stack[0].m_obj;
lean_object* v_res_1308_;
v_res_1308_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_1303_);
stack->m_obj
 = v_res_1308_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2___boxed(lean_object* v_s_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v_s_1309_);
return v_res_1311_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1351_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_projectDir_1352_; lean_object* v_leanPrefix_1353_; lean_object* v_whichLake_1354_; lean_object* v_lakeHome_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___y_1359_; lean_object* v_leanPrefix_1360_; lean_object* v_whichLake_1361_; lean_object* v_lakeHome_1362_; uint8_t v___x_1417_; 
lean_dec_ref_known(v___x_1351_, 1);
v_projectDir_1352_ = lean_ctor_get(v_a_1345_, 0);
v_leanPrefix_1353_ = lean_ctor_get(v_a_1345_, 6);
v_whichLake_1354_ = lean_ctor_get(v_a_1345_, 10);
v_lakeHome_1355_ = lean_ctor_get(v_a_1345_, 11);
v___x_1356_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1352_);
v___x_1357_ = l_System_FilePath_join(v_projectDir_1352_, v___x_1356_);
v___x_1417_ = l_System_FilePath_pathExists(v___x_1357_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_io_create_dir(v___x_1357_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_dec_ref_known(v___x_1418_, 1);
v___y_1359_ = v_a_1345_;
v_leanPrefix_1360_ = v_leanPrefix_1353_;
v_whichLake_1361_ = v_whichLake_1354_;
v_lakeHome_1362_ = v_lakeHome_1355_;
goto v___jp_1358_;
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v___x_1357_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
v___y_1359_ = v_a_1345_;
v_leanPrefix_1360_ = v_leanPrefix_1353_;
v_whichLake_1361_ = v_whichLake_1354_;
v_lakeHome_1362_ = v_lakeHome_1355_;
goto v___jp_1358_;
}
v___jp_1358_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1363_ = lean_unsigned_to_nat(1u);
v___x_1364_ = lean_mk_empty_array_with_capacity(v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__5));
v___x_1366_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1367_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1368_ = lean_unsigned_to_nat(3u);
v___x_1369_ = lean_mk_empty_array_with_capacity(v___x_1368_);
lean_inc_ref(v_projectDir_1352_);
v___x_1370_ = lean_array_push(v___x_1369_, v_projectDir_1352_);
lean_inc_ref(v_leanPrefix_1360_);
v___x_1371_ = lean_array_push(v___x_1370_, v_leanPrefix_1360_);
lean_inc_ref(v_lakeHome_1362_);
v___x_1372_ = lean_array_push(v___x_1371_, v_lakeHome_1362_);
v___x_1373_ = lean_array_push(v___x_1364_, v___x_1357_);
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1376_ = 1;
v___x_1377_ = lean_box(0);
lean_inc_ref(v_whichLake_1361_);
v___x_1378_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1378_, 0, v_whichLake_1361_);
lean_ctor_set(v___x_1378_, 1, v___x_1365_);
lean_ctor_set(v___x_1378_, 2, v___x_1366_);
lean_ctor_set(v___x_1378_, 3, v___x_1367_);
lean_ctor_set(v___x_1378_, 4, v___x_1372_);
lean_ctor_set(v___x_1378_, 5, v___x_1373_);
lean_ctor_set(v___x_1378_, 6, v___x_1375_);
lean_ctor_set(v___x_1378_, 7, v___x_1377_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*8, v___x_1376_);
v___x_1379_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdout(v___x_1378_, v___y_1359_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1408_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_n(v_a_1380_, 2);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = lean_string_utf8_byte_size(v_a_1380_);
v___x_1382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1382_, 0, v_a_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1374_);
lean_ctor_set(v___x_1382_, 2, v___x_1381_);
v___x_1383_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__3___closed__0);
v___x_1384_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1380_, v___x_1382_, v___x_1381_, v___x_1383_, v___x_1375_);
lean_dec_ref_known(v___x_1382_, 3);
v___x_1385_ = lean_array_to_list(v___x_1384_);
v___x_1386_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__15));
v___x_1387_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v___x_1385_, v___x_1386_);
lean_dec(v___x_1385_);
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1408_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1408_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v_fst_1392_; lean_object* v_snd_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1407_; 
v_fst_1392_ = lean_ctor_get(v_a_1388_, 0);
v_snd_1393_ = lean_ctor_get(v_a_1388_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_a_1388_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1395_ = v_a_1388_;
v_isShared_1396_ = v_isSharedCheck_1407_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_snd_1393_);
lean_inc(v_fst_1392_);
lean_dec(v_a_1388_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1407_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = lean_string_utf8_byte_size(v_fst_1392_);
v___x_1398_ = lean_nat_dec_eq(v___x_1397_, v___x_1374_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_string_utf8_byte_size(v_snd_1393_);
v___x_1400_ = lean_nat_dec_eq(v___x_1399_, v___x_1374_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1402_; 
if (v_isShared_1396_ == 0)
{
v___x_1402_ = v___x_1395_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_fst_1392_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_snd_1393_);
v___x_1402_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1402_);
v___x_1404_ = v___x_1390_;
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
else
{
lean_del_object(v___x_1395_);
lean_dec(v_snd_1393_);
lean_dec(v_fst_1392_);
lean_del_object(v___x_1390_);
goto v___jp_1347_;
}
}
else
{
lean_del_object(v___x_1395_);
lean_dec(v_snd_1393_);
lean_dec(v_fst_1392_);
lean_del_object(v___x_1390_);
goto v___jp_1347_;
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1379_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1379_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1351_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1351_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
v___jp_1347_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__1));
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1345_ = stack[0].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_1345_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___boxed(lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v_a_1436_);
lean_dec_ref(v_a_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(lean_object* v_a_1439_, lean_object* v___x_1440_, lean_object* v___x_1441_, lean_object* v_inst_1442_, lean_object* v_R_1443_, lean_object* v_a_1444_, lean_object* v_b_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___redArg(v_a_1439_, v___x_1440_, v___x_1441_, v_a_1444_, v_b_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4___boxed(lean_object* v_a_1447_, lean_object* v___x_1448_, lean_object* v___x_1449_, lean_object* v_inst_1450_, lean_object* v_R_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__4(v_a_1447_, v___x_1448_, v___x_1449_, v_inst_1450_, v_R_1451_, v_a_1452_, v_b_1453_);
lean_dec_ref(v___x_1448_);
return v_res_1454_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(lean_object* v_as_1455_, lean_object* v_as_x27_1456_, lean_object* v_b_1457_, lean_object* v_a_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___redArg(v_as_x27_1456_, v_b_1457_);
return v___x_1461_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1455_ = stack[0].m_obj;
lean_object* v_as_x27_1456_ = stack[1].m_obj;
lean_object* v_b_1457_ = stack[2].m_obj;
lean_object* v___y_1459_ = stack[4].m_obj;
lean_object* v_res_1462_;
v_res_1462_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_1455_, v_as_x27_1456_, v_b_1457_, lean_box(0), v___y_1459_);
stack->m_obj
 = v_res_1462_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5___boxed(lean_object* v_as_1463_, lean_object* v_as_x27_1464_, lean_object* v_b_1465_, lean_object* v_a_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_List_forIn_x27_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__5(v_as_1463_, v_as_x27_1464_, v_b_1465_, v_a_1466_, v___y_1467_);
lean_dec_ref(v___y_1467_);
lean_dec(v_as_x27_1464_);
lean_dec(v_as_1463_);
return v_res_1469_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__2));
v___x_1486_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_projectDir_1487_; lean_object* v_leanPrefix_1488_; lean_object* v_whichLake_1489_; lean_object* v_lakeHome_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___y_1494_; lean_object* v_leanPrefix_1495_; lean_object* v_whichLake_1496_; lean_object* v_lakeHome_1497_; uint8_t v___x_1514_; 
lean_dec_ref_known(v___x_1486_, 1);
v_projectDir_1487_ = lean_ctor_get(v_a_1483_, 0);
v_leanPrefix_1488_ = lean_ctor_get(v_a_1483_, 6);
v_whichLake_1489_ = lean_ctor_get(v_a_1483_, 10);
v_lakeHome_1490_ = lean_ctor_get(v_a_1483_, 11);
v___x_1491_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1487_);
v___x_1492_ = l_System_FilePath_join(v_projectDir_1487_, v___x_1491_);
v___x_1514_ = l_System_FilePath_pathExists(v___x_1492_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_io_create_dir(v___x_1492_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_dec_ref_known(v___x_1515_, 1);
v___y_1494_ = v_a_1483_;
v_leanPrefix_1495_ = v_leanPrefix_1488_;
v_whichLake_1496_ = v_whichLake_1489_;
v_lakeHome_1497_ = v_lakeHome_1490_;
goto v___jp_1493_;
}
else
{
lean_dec_ref(v___x_1492_);
return v___x_1515_;
}
}
else
{
v___y_1494_ = v_a_1483_;
v_leanPrefix_1495_ = v_leanPrefix_1488_;
v_whichLake_1496_ = v_whichLake_1489_;
v_lakeHome_1497_ = v_lakeHome_1490_;
goto v___jp_1493_;
}
v___jp_1493_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_mk_empty_array_with_capacity(v___x_1498_);
v___x_1500_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__1));
v___x_1501_ = lean_unsigned_to_nat(3u);
v___x_1502_ = lean_mk_empty_array_with_capacity(v___x_1501_);
v___x_1503_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1504_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
lean_inc_ref(v_projectDir_1487_);
v___x_1505_ = lean_array_push(v___x_1502_, v_projectDir_1487_);
lean_inc_ref(v_leanPrefix_1495_);
v___x_1506_ = lean_array_push(v___x_1505_, v_leanPrefix_1495_);
lean_inc_ref(v_lakeHome_1497_);
v___x_1507_ = lean_array_push(v___x_1506_, v_lakeHome_1497_);
v___x_1508_ = lean_array_push(v___x_1499_, v___x_1492_);
v___x_1509_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1510_ = 1;
v___x_1511_ = lean_box(0);
lean_inc_ref(v_whichLake_1496_);
v___x_1512_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1512_, 0, v_whichLake_1496_);
lean_ctor_set(v___x_1512_, 1, v___x_1500_);
lean_ctor_set(v___x_1512_, 2, v___x_1503_);
lean_ctor_set(v___x_1512_, 3, v___x_1504_);
lean_ctor_set(v___x_1512_, 4, v___x_1507_);
lean_ctor_set(v___x_1512_, 5, v___x_1508_);
lean_ctor_set(v___x_1512_, 6, v___x_1509_);
lean_ctor_set(v___x_1512_, 7, v___x_1511_);
lean_ctor_set_uint8(v___x_1512_, sizeof(void*)*8, v___x_1510_);
v___x_1513_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1512_, v___y_1494_);
return v___x_1513_;
}
}
else
{
return v___x_1486_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1483_ = stack[0].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_1483_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___boxed(lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_1517_);
lean_dec_ref(v_a_1517_);
return v_res_1519_;
}
}
lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(lean_object* v_f_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v_fst_1534_; lean_object* v_snd_1535_; lean_object* v_r_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v_fst_1534_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_fst_1534_);
v_snd_1535_ = lean_ctor_get(v_a_1533_, 1);
lean_inc_n(v_snd_1535_, 2);
lean_dec(v_a_1533_);
lean_inc_ref(v___y_1530_);
v_r_1536_ = lean_apply_4(v_f_1529_, v_fst_1534_, v_snd_1535_, v___y_1530_, lean_box(0));
if (lean_obj_tag(v_r_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v_r_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v_r_1536_, 1);
v___x_1538_ = lean_io_remove_file(v_snd_1535_);
lean_dec(v_snd_1535_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1546_);
v___x_1540_ = v___x_1538_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v___x_1538_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_a_1537_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1537_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_a_1537_);
v_a_1547_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1538_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1538_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v_r_1536_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v_r_1536_, 1);
v___x_1556_ = lean_io_remove_file(v_snd_1535_);
lean_dec(v_snd_1535_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v___x_1556_, 0);
lean_dec(v_unused_1564_);
v___x_1558_ = v___x_1556_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_dec(v___x_1556_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 1);
lean_ctor_set(v___x_1558_, 0, v_a_1555_);
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1555_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1555_);
v_a_1565_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1556_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1556_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_f_1529_);
v_a_1573_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1532_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1532_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1529_ = stack[0].m_obj;
lean_object* v___y_1530_ = stack[1].m_obj;
lean_object* v_res_1581_;
v_res_1581_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1529_, v___y_1530_);
stack->m_obj
 = v_res_1581_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg___boxed(lean_object* v_f_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1582_, v___y_1583_);
lean_dec_ref(v___y_1583_);
return v_res_1585_;
}
}
lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(lean_object* v_00_u03b1_1586_, lean_object* v_f_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v_f_1587_, v___y_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT void l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1587_ = stack[1].m_obj;
lean_object* v___y_1588_ = stack[2].m_obj;
lean_object* v_res_1591_;
v_res_1591_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(lean_box(0), v_f_1587_, v___y_1588_);
stack->m_obj
 = v_res_1591_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_f_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1(v_00_u03b1_1592_, v_f_1593_, v___y_1594_);
lean_dec_ref(v___y_1594_);
return v_res_1596_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(lean_object* v_projectDir_1612_, lean_object* v_f_1613_, lean_object* v_handle_1614_, lean_object* v_path_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_leanPrefix_1618_; lean_object* v_whichLake_1619_; lean_object* v_lakeHome_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_leanPrefix_1618_ = lean_ctor_get(v___y_1616_, 6);
v_whichLake_1619_ = lean_ctor_get(v___y_1616_, 10);
v_lakeHome_1620_ = lean_ctor_get(v___y_1616_, 11);
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = lean_mk_empty_array_with_capacity(v___x_1621_);
v___x_1623_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__1));
v___x_1624_ = lean_unsigned_to_nat(3u);
v___x_1625_ = lean_mk_empty_array_with_capacity(v___x_1624_);
v___x_1626_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps___closed__2));
v___x_1627_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__4));
lean_inc_ref(v_projectDir_1612_);
v___x_1628_ = lean_array_push(v___x_1625_, v_projectDir_1612_);
lean_inc_ref(v_leanPrefix_1618_);
v___x_1629_ = lean_array_push(v___x_1628_, v_leanPrefix_1618_);
lean_inc_ref(v_lakeHome_1620_);
v___x_1630_ = lean_array_push(v___x_1629_, v_lakeHome_1620_);
v___x_1631_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
v___x_1632_ = l_System_FilePath_join(v_projectDir_1612_, v___x_1631_);
v___x_1633_ = lean_array_push(v___x_1622_, v___x_1632_);
v___x_1634_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1635_ = 0;
v___x_1636_ = lean_box(0);
lean_inc_ref(v_whichLake_1619_);
v___x_1637_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1637_, 0, v_whichLake_1619_);
lean_ctor_set(v___x_1637_, 1, v___x_1623_);
lean_ctor_set(v___x_1637_, 2, v___x_1626_);
lean_ctor_set(v___x_1637_, 3, v___x_1627_);
lean_ctor_set(v___x_1637_, 4, v___x_1630_);
lean_ctor_set(v___x_1637_, 5, v___x_1633_);
lean_ctor_set(v___x_1637_, 6, v___x_1634_);
lean_ctor_set(v___x_1637_, 7, v___x_1636_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*8, v___x_1635_);
v___x_1638_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_handle_1614_, v___x_1637_, v___y_1616_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref_known(v___x_1638_, 1);
lean_inc_ref(v___y_1616_);
v___x_1639_ = lean_apply_3(v_f_1613_, v_path_1615_, v___y_1616_, lean_box(0));
return v___x_1639_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v_path_1615_);
lean_dec_ref(v_f_1613_);
v_a_1640_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1638_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1638_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_projectDir_1612_ = stack[0].m_obj;
lean_object* v_f_1613_ = stack[1].m_obj;
lean_object* v_handle_1614_ = stack[2].m_obj;
lean_object* v_path_1615_ = stack[3].m_obj;
lean_object* v___y_1616_ = stack[4].m_obj;
lean_object* v_res_1648_;
v_res_1648_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(v_projectDir_1612_, v_f_1613_, v_handle_1614_, v_path_1615_, v___y_1616_);
stack->m_obj
 = v_res_1648_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed(lean_object* v_projectDir_1649_, lean_object* v_f_1650_, lean_object* v_handle_1651_, lean_object* v_path_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0(v_projectDir_1649_, v_f_1650_, v_handle_1651_, v_path_1652_, v___y_1653_);
lean_dec_ref(v___y_1653_);
return v_res_1655_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(uint8_t v_a_1656_, lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_box(0);
return v___x_1658_;
}
else
{
lean_object* v_key_1659_; lean_object* v_value_1660_; lean_object* v_tail_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_key_1659_ = lean_ctor_get(v_x_1657_, 0);
v_value_1660_ = lean_ctor_get(v_x_1657_, 1);
v_tail_1661_ = lean_ctor_get(v_x_1657_, 2);
v___x_1662_ = lean_obj_tag_nat(v_key_1659_);
v___x_1663_ = lean_box(v_a_1656_);
v___x_1664_ = lean_obj_tag_nat(v___x_1663_);
lean_dec(v___x_1663_);
v___x_1665_ = lean_nat_dec_eq(v___x_1662_, v___x_1664_);
if (v___x_1665_ == 0)
{
v_x_1657_ = v_tail_1661_;
goto _start;
}
else
{
lean_object* v___x_1667_; 
lean_inc(v_value_1660_);
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_value_1660_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1656_ = stack[0].m_num;
lean_object* v_x_1657_ = stack[1].m_obj;
lean_object* v_res_1668_;
v_res_1668_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1656_, v_x_1657_);
stack->m_obj
 = v_res_1668_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg___boxed(lean_object* v_a_1669_, lean_object* v_x_1670_){
_start:
{
uint8_t v_a_boxed_1671_; lean_object* v_res_1672_; 
v_a_boxed_1671_ = lean_unbox(v_a_1669_);
v_res_1672_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_boxed_1671_, v_x_1670_);
lean_dec(v_x_1670_);
return v_res_1672_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(lean_object* v_m_1673_, uint8_t v_a_1674_){
_start:
{
lean_object* v_buckets_1675_; lean_object* v___x_1676_; uint64_t v___x_1677_; uint64_t v___x_1678_; uint64_t v___x_1679_; uint64_t v_fold_1680_; uint64_t v___x_1681_; uint64_t v___x_1682_; uint64_t v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_buckets_1675_ = lean_ctor_get(v_m_1673_, 1);
v___x_1676_ = lean_array_get_size(v_buckets_1675_);
v___x_1677_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_1674_);
v___x_1678_ = 32ULL;
v___x_1679_ = lean_uint64_shift_right(v___x_1677_, v___x_1678_);
v_fold_1680_ = lean_uint64_xor(v___x_1677_, v___x_1679_);
v___x_1681_ = 16ULL;
v___x_1682_ = lean_uint64_shift_right(v_fold_1680_, v___x_1681_);
v___x_1683_ = lean_uint64_xor(v_fold_1680_, v___x_1682_);
v___x_1684_ = lean_uint64_to_usize(v___x_1683_);
v___x_1685_ = lean_usize_of_nat(v___x_1676_);
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_sub(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_usize_land(v___x_1684_, v___x_1687_);
v___x_1689_ = lean_array_uget_borrowed(v_buckets_1675_, v___x_1688_);
v___x_1690_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1674_, v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1673_ = stack[0].m_obj;
uint8_t v_a_1674_ = stack[1].m_num;
lean_object* v_res_1691_;
v_res_1691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1673_, v_a_1674_);
stack->m_obj
 = v_res_1691_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg___boxed(lean_object* v_m_1692_, lean_object* v_a_1693_){
_start:
{
uint8_t v_a_boxed_1694_; lean_object* v_res_1695_; 
v_a_boxed_1694_ = lean_unbox(v_a_1693_);
v_res_1695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1692_, v_a_boxed_1694_);
lean_dec_ref(v_m_1692_);
return v_res_1695_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(lean_object* v_f_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_projectDir_1700_; lean_object* v_moduleStore_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; 
v_projectDir_1700_ = lean_ctor_get(v_a_1698_, 0);
v_moduleStore_1701_ = lean_ctor_get(v_a_1698_, 17);
v___x_1702_ = 0;
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_1701_, v___x_1702_);
if (lean_obj_tag(v___x_1703_) == 1)
{
lean_object* v_val_1704_; lean_object* v___x_1705_; 
v_val_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v___x_1703_, 1);
lean_inc_ref(v_a_1698_);
v___x_1705_ = lean_apply_3(v_f_1697_, v_val_1704_, v_a_1698_, lean_box(0));
return v___x_1705_;
}
else
{
lean_object* v___f_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec(v___x_1703_);
lean_inc_ref(v_projectDir_1700_);
v___f_1706_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_1706_, 0, v_projectDir_1700_);
lean_closure_set(v___f_1706_, 1, v_f_1697_);
v___x_1707_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___closed__0));
v___x_1708_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1707_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1708_, 1);
v___x_1709_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1706_, v_a_1698_);
return v___x_1709_;
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref(v___f_1706_);
v_a_1710_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1708_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1697_ = stack[0].m_obj;
lean_object* v_a_1698_ = stack[1].m_obj;
lean_object* v_res_1718_;
v_res_1718_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1697_, v_a_1698_);
stack->m_obj
 = v_res_1718_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___boxed(lean_object* v_f_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1719_, v_a_1720_);
lean_dec_ref(v_a_1720_);
return v_res_1722_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(lean_object* v_00_u03b1_1723_, lean_object* v_f_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v_f_1724_, v_a_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1724_ = stack[1].m_obj;
lean_object* v_a_1725_ = stack[2].m_obj;
lean_object* v_res_1728_;
v_res_1728_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(lean_box(0), v_f_1724_, v_a_1725_);
stack->m_obj
 = v_res_1728_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_f_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport(v_00_u03b1_1729_, v_f_1730_, v_a_1731_);
lean_dec_ref(v_a_1731_);
return v_res_1733_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(lean_object* v_00_u03b2_1734_, lean_object* v_m_1735_, uint8_t v_a_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_m_1735_, v_a_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1735_ = stack[1].m_obj;
uint8_t v_a_1736_ = stack[2].m_num;
lean_object* v_res_1738_;
v_res_1738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(lean_box(0), v_m_1735_, v_a_1736_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___boxed(lean_object* v_00_u03b2_1739_, lean_object* v_m_1740_, lean_object* v_a_1741_){
_start:
{
uint8_t v_a_boxed_1742_; lean_object* v_res_1743_; 
v_a_boxed_1742_ = lean_unbox(v_a_1741_);
v_res_1743_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0(v_00_u03b2_1739_, v_m_1740_, v_a_boxed_1742_);
lean_dec_ref(v_m_1740_);
return v_res_1743_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(lean_object* v_00_u03b2_1744_, uint8_t v_a_1745_, lean_object* v_x_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___redArg(v_a_1745_, v_x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1745_ = stack[1].m_num;
lean_object* v_x_1746_ = stack[2].m_obj;
lean_object* v_res_1748_;
v_res_1748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(lean_box(0), v_a_1745_, v_x_1746_);
stack->m_obj
 = v_res_1748_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1749_, lean_object* v_a_1750_, lean_object* v_x_1751_){
_start:
{
uint8_t v_a_boxed_1752_; lean_object* v_res_1753_; 
v_a_boxed_1752_ = lean_unbox(v_a_1750_);
v_res_1753_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0_spec__0(v_00_u03b2_1749_, v_a_boxed_1752_, v_x_1751_);
lean_dec(v_x_1751_);
return v_res_1753_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(size_t v_sz_1754_, size_t v_i_1755_, lean_object* v_bs_1756_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_lt(v_i_1755_, v_sz_1754_);
if (v___x_1757_ == 0)
{
return v_bs_1756_;
}
else
{
lean_object* v_v_1758_; lean_object* v___x_1759_; lean_object* v_bs_x27_1760_; lean_object* v___x_1761_; size_t v___x_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v_v_1758_ = lean_array_uget(v_bs_1756_, v_i_1755_);
v___x_1759_ = lean_unsigned_to_nat(0u);
v_bs_x27_1760_ = lean_array_uset(v_bs_1756_, v_i_1755_, v___x_1759_);
v___x_1761_ = l_Lean_Name_toString(v_v_1758_, v___x_1757_);
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1755_, v___x_1762_);
v___x_1764_ = lean_array_uset(v_bs_x27_1760_, v_i_1755_, v___x_1761_);
v_i_1755_ = v___x_1763_;
v_bs_1756_ = v___x_1764_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1754_ = stack[0].m_num;
size_t v_i_1755_ = stack[1].m_num;
lean_object* v_bs_1756_ = stack[2].m_obj;
lean_object* v_res_1766_;
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_1754_, v_i_1755_, v_bs_1756_);
stack->m_obj
 = v_res_1766_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0___boxed(lean_object* v_sz_1767_, lean_object* v_i_1768_, lean_object* v_bs_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1767_);
lean_dec(v_sz_1767_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_boxed_1770_, v_i_boxed_1771_, v_bs_1769_);
return v_res_1772_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(lean_object* v_targets_1780_, lean_object* v_a_1781_){
_start:
{
size_t v_sz_1783_; size_t v___x_1784_; lean_object* v_targetArgs_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_targetList_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_sz_1783_ = lean_array_size(v_targets_1780_);
v___x_1784_ = ((size_t)0ULL);
v_targetArgs_1785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_spec__0(v_sz_1783_, v___x_1784_, v_targets_1780_);
v___x_1786_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
lean_inc_ref(v_targetArgs_1785_);
v___x_1787_ = lean_array_to_list(v_targetArgs_1785_);
v_targetList_1788_ = l_String_intercalate(v___x_1786_, v___x_1787_);
v___x_1789_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__1));
v___x_1790_ = lean_string_append(v___x_1789_, v_targetList_1788_);
lean_dec_ref(v_targetList_1788_);
v___x_1791_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1790_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_projectDir_1792_; lean_object* v_leanPrefix_1793_; lean_object* v_whichLake_1794_; lean_object* v_lakeHome_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___y_1799_; lean_object* v_leanPrefix_1800_; lean_object* v_whichLake_1801_; lean_object* v_lakeHome_1802_; uint8_t v___x_1820_; 
lean_dec_ref_known(v___x_1791_, 1);
v_projectDir_1792_ = lean_ctor_get(v_a_1781_, 0);
v_leanPrefix_1793_ = lean_ctor_get(v_a_1781_, 6);
v_whichLake_1794_ = lean_ctor_get(v_a_1781_, 10);
v_lakeHome_1795_ = lean_ctor_get(v_a_1781_, 11);
v___x_1796_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1792_);
v___x_1797_ = l_System_FilePath_join(v_projectDir_1792_, v___x_1796_);
v___x_1820_ = l_System_FilePath_pathExists(v___x_1797_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
v___x_1821_ = lean_io_create_dir(v___x_1797_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_dec_ref_known(v___x_1821_, 1);
v___y_1799_ = v_a_1781_;
v_leanPrefix_1800_ = v_leanPrefix_1793_;
v_whichLake_1801_ = v_whichLake_1794_;
v_lakeHome_1802_ = v_lakeHome_1795_;
goto v___jp_1798_;
}
else
{
lean_dec_ref(v___x_1797_);
lean_dec_ref(v_targetArgs_1785_);
return v___x_1821_;
}
}
else
{
v___y_1799_ = v_a_1781_;
v_leanPrefix_1800_ = v_leanPrefix_1793_;
v_whichLake_1801_ = v_whichLake_1794_;
v_lakeHome_1802_ = v_lakeHome_1795_;
goto v___jp_1798_;
}
v___jp_1798_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_mk_empty_array_with_capacity(v___x_1803_);
v___x_1805_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__3));
v___x_1806_ = l_Array_append___redArg(v___x_1805_, v_targetArgs_1785_);
lean_dec_ref(v_targetArgs_1785_);
v___x_1807_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__8));
v___x_1808_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_1809_ = lean_unsigned_to_nat(3u);
v___x_1810_ = lean_mk_empty_array_with_capacity(v___x_1809_);
lean_inc_ref(v_projectDir_1792_);
v___x_1811_ = lean_array_push(v___x_1810_, v_projectDir_1792_);
lean_inc_ref(v_leanPrefix_1800_);
v___x_1812_ = lean_array_push(v___x_1811_, v_leanPrefix_1800_);
lean_inc_ref(v_lakeHome_1802_);
v___x_1813_ = lean_array_push(v___x_1812_, v_lakeHome_1802_);
v___x_1814_ = lean_array_push(v___x_1804_, v___x_1797_);
v___x_1815_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1816_ = 0;
v___x_1817_ = lean_box(0);
lean_inc_ref(v_whichLake_1801_);
v___x_1818_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1818_, 0, v_whichLake_1801_);
lean_ctor_set(v___x_1818_, 1, v___x_1806_);
lean_ctor_set(v___x_1818_, 2, v___x_1807_);
lean_ctor_set(v___x_1818_, 3, v___x_1808_);
lean_ctor_set(v___x_1818_, 4, v___x_1813_);
lean_ctor_set(v___x_1818_, 5, v___x_1814_);
lean_ctor_set(v___x_1818_, 6, v___x_1815_);
lean_ctor_set(v___x_1818_, 7, v___x_1817_);
lean_ctor_set_uint8(v___x_1818_, sizeof(void*)*8, v___x_1816_);
v___x_1819_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxed(v___x_1818_, v___y_1799_);
return v___x_1819_;
}
}
else
{
lean_dec_ref(v_targetArgs_1785_);
return v___x_1791_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild_0interp(lean_interpreter_value* stack)
{
lean_object* v_targets_1780_ = stack[0].m_obj;
lean_object* v_a_1781_ = stack[1].m_obj;
lean_object* v_res_1822_;
v_res_1822_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_1780_, v_a_1781_);
stack->m_obj
 = v_res_1822_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___boxed(lean_object* v_targets_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v_targets_1823_, v_a_1824_);
lean_dec_ref(v_a_1824_);
return v_res_1826_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1836_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__11));
v___x_1837_ = lean_unsigned_to_nat(3u);
v___x_1838_ = lean_mk_empty_array_with_capacity(v___x_1837_);
v___x_1839_ = lean_array_push(v___x_1838_, v___x_1836_);
return v___x_1839_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(lean_object* v_projectDir_1840_, lean_object* v_whichLean4Export_1841_, lean_object* v_args_1842_, lean_object* v_f_1843_, lean_object* v_exportHandle_1844_, lean_object* v_exportPath_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_leanPrefix_1848_; lean_object* v_leanPath_1849_; lean_object* v_binPath_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_leanPrefix_1848_ = lean_ctor_get(v___y_1846_, 6);
v_leanPath_1849_ = lean_ctor_get(v___y_1846_, 7);
v_binPath_1850_ = lean_ctor_get(v___y_1846_, 8);
v___x_1851_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__6));
v___x_1852_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__0));
v___x_1853_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__1));
lean_inc_ref(v_leanPath_1849_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_leanPath_1849_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1852_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
lean_inc_ref(v_binPath_1850_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_binPath_1850_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1851_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___closed__2);
v___x_1859_ = lean_array_push(v___x_1858_, v___x_1855_);
v___x_1860_ = lean_array_push(v___x_1859_, v___x_1857_);
v___x_1861_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__3));
lean_inc_ref(v_projectDir_1840_);
v___x_1862_ = l_System_FilePath_join(v_projectDir_1840_, v___x_1861_);
v___x_1863_ = lean_unsigned_to_nat(4u);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___x_1863_);
v___x_1865_ = lean_array_push(v___x_1864_, v_projectDir_1840_);
v___x_1866_ = lean_array_push(v___x_1865_, v___x_1862_);
lean_inc_ref(v_leanPrefix_1848_);
v___x_1867_ = lean_array_push(v___x_1866_, v_leanPrefix_1848_);
lean_inc_ref(v_whichLean4Export_1841_);
v___x_1868_ = lean_array_push(v___x_1867_, v_whichLean4Export_1841_);
v___x_1869_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_1870_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_1871_ = 0;
v___x_1872_ = lean_box(0);
v___x_1873_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1873_, 0, v_whichLean4Export_1841_);
lean_ctor_set(v___x_1873_, 1, v_args_1842_);
lean_ctor_set(v___x_1873_, 2, v___x_1853_);
lean_ctor_set(v___x_1873_, 3, v___x_1860_);
lean_ctor_set(v___x_1873_, 4, v___x_1868_);
lean_ctor_set(v___x_1873_, 5, v___x_1869_);
lean_ctor_set(v___x_1873_, 6, v___x_1870_);
lean_ctor_set(v___x_1873_, 7, v___x_1872_);
lean_ctor_set_uint8(v___x_1873_, sizeof(void*)*8, v___x_1871_);
v___x_1874_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo(v_exportHandle_1844_, v___x_1873_, v___y_1846_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v___x_1875_; 
lean_dec_ref_known(v___x_1874_, 1);
lean_inc_ref(v___y_1846_);
v___x_1875_ = lean_apply_3(v_f_1843_, v_exportPath_1845_, v___y_1846_, lean_box(0));
return v___x_1875_;
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_exportPath_1845_);
lean_dec_ref(v_f_1843_);
v_a_1876_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1874_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_projectDir_1840_ = stack[0].m_obj;
lean_object* v_whichLean4Export_1841_ = stack[1].m_obj;
lean_object* v_args_1842_ = stack[2].m_obj;
lean_object* v_f_1843_ = stack[3].m_obj;
lean_object* v_exportHandle_1844_ = stack[4].m_obj;
lean_object* v_exportPath_1845_ = stack[5].m_obj;
lean_object* v___y_1846_ = stack[6].m_obj;
lean_object* v_res_1884_;
v_res_1884_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(v_projectDir_1840_, v_whichLean4Export_1841_, v_args_1842_, v_f_1843_, v_exportHandle_1844_, v_exportPath_1845_, v___y_1846_);
stack->m_obj
 = v_res_1884_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed(lean_object* v_projectDir_1885_, lean_object* v_whichLean4Export_1886_, lean_object* v_args_1887_, lean_object* v_f_1888_, lean_object* v_exportHandle_1889_, lean_object* v_exportPath_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0(v_projectDir_1885_, v_whichLean4Export_1886_, v_args_1887_, v_f_1888_, v_exportHandle_1889_, v_exportPath_1890_, v___y_1891_);
lean_dec_ref(v___y_1891_);
return v_res_1893_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(lean_object* v_args_1894_, lean_object* v_f_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_projectDir_1898_; lean_object* v_whichLean4Export_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; 
v_projectDir_1898_ = lean_ctor_get(v_a_1896_, 0);
v_whichLean4Export_1899_ = lean_ctor_get(v_a_1896_, 12);
lean_inc_ref(v_whichLean4Export_1899_);
lean_inc_ref(v_projectDir_1898_);
v___f_1900_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_1900_, 0, v_projectDir_1898_);
lean_closure_set(v___f_1900_, 1, v_whichLean4Export_1899_);
lean_closure_set(v___f_1900_, 2, v_args_1894_);
lean_closure_set(v___f_1900_, 3, v_f_1895_);
v___x_1901_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_1900_, v_a_1896_);
return v___x_1901_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1894_ = stack[0].m_obj;
lean_object* v_f_1895_ = stack[1].m_obj;
lean_object* v_a_1896_ = stack[2].m_obj;
lean_object* v_res_1902_;
v_res_1902_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1894_, v_f_1895_, v_a_1896_);
stack->m_obj
 = v_res_1902_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg___boxed(lean_object* v_args_1903_, lean_object* v_f_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1903_, v_f_1904_, v_a_1905_);
lean_dec_ref(v_a_1905_);
return v_res_1907_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_object* v_00_u03b1_1908_, lean_object* v_args_1909_, lean_object* v_f_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v_args_1909_, v_f_1910_, v_a_1911_);
return v___x_1913_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1909_ = stack[1].m_obj;
lean_object* v_f_1910_ = stack[2].m_obj;
lean_object* v_a_1911_ = stack[3].m_obj;
lean_object* v_res_1914_;
v_res_1914_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(lean_box(0), v_args_1909_, v_f_1910_, v_a_1911_);
stack->m_obj
 = v_res_1914_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_args_1916_, lean_object* v_f_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter(v_00_u03b1_1915_, v_args_1916_, v_f_1917_, v_a_1918_);
lean_dec_ref(v_a_1918_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
return v_x_1922_;
}
else
{
lean_object* v_head_1924_; lean_object* v_tail_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_head_1924_ = lean_ctor_get(v_x_1923_, 0);
lean_inc(v_head_1924_);
v_tail_1925_ = lean_ctor_get(v_x_1923_, 1);
lean_inc(v_tail_1925_);
lean_dec_ref_known(v_x_1923_, 2);
v___x_1926_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
v___x_1927_ = lean_string_append(v_x_1922_, v___x_1926_);
v___x_1928_ = 1;
v___x_1929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1924_, v___x_1928_);
v___x_1930_ = lean_string_append(v___x_1927_, v___x_1929_);
lean_dec_ref(v___x_1929_);
v_x_1922_ = v___x_1930_;
v_x_1923_ = v_tail_1925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(lean_object* v_x_1935_){
_start:
{
if (lean_obj_tag(v_x_1935_) == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__0));
return v___x_1936_;
}
else
{
lean_object* v_tail_1937_; 
v_tail_1937_ = lean_ctor_get(v_x_1935_, 1);
if (lean_obj_tag(v_tail_1937_) == 0)
{
lean_object* v_head_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_head_1938_ = lean_ctor_get(v_x_1935_, 0);
lean_inc(v_head_1938_);
lean_dec_ref_known(v_x_1935_, 2);
v___x_1939_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1940_ = 1;
v___x_1941_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1938_, v___x_1940_);
v___x_1942_ = lean_string_append(v___x_1939_, v___x_1941_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__2));
v___x_1944_ = lean_string_append(v___x_1942_, v___x_1943_);
return v___x_1944_;
}
else
{
lean_object* v_head_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint32_t v___x_1951_; lean_object* v___x_1952_; 
lean_inc(v_tail_1937_);
v_head_1945_ = lean_ctor_get(v_x_1935_, 0);
lean_inc(v_head_1945_);
lean_dec_ref_known(v_x_1935_, 2);
v___x_1946_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_1947_ = 1;
v___x_1948_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1945_, v___x_1947_);
v___x_1949_ = lean_string_append(v___x_1946_, v___x_1948_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0(v___x_1949_, v_tail_1937_);
v___x_1951_ = 93;
v___x_1952_ = lean_string_push(v___x_1950_, v___x_1951_);
return v___x_1952_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(size_t v_sz_1953_, size_t v_i_1954_, lean_object* v_bs_1955_){
_start:
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_usize_dec_lt(v_i_1954_, v_sz_1953_);
if (v___x_1956_ == 0)
{
return v_bs_1955_;
}
else
{
lean_object* v_v_1957_; lean_object* v___x_1958_; lean_object* v_bs_x27_1959_; lean_object* v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
v_v_1957_ = lean_array_uget(v_bs_1955_, v_i_1954_);
v___x_1958_ = lean_unsigned_to_nat(0u);
v_bs_x27_1959_ = lean_array_uset(v_bs_1955_, v_i_1954_, v___x_1958_);
v___x_1960_ = l_Lean_Name_toString(v_v_1957_, v___x_1956_);
v___x_1961_ = ((size_t)1ULL);
v___x_1962_ = lean_usize_add(v_i_1954_, v___x_1961_);
v___x_1963_ = lean_array_uset(v_bs_x27_1959_, v_i_1954_, v___x_1960_);
v_i_1954_ = v___x_1962_;
v_bs_1955_ = v___x_1963_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1953_ = stack[0].m_num;
size_t v_i_1954_ = stack[1].m_num;
lean_object* v_bs_1955_ = stack[2].m_obj;
lean_object* v_res_1965_;
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_1953_, v_i_1954_, v_bs_1955_);
stack->m_obj
 = v_res_1965_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1___boxed(lean_object* v_sz_1966_, lean_object* v_i_1967_, lean_object* v_bs_1968_){
_start:
{
size_t v_sz_boxed_1969_; size_t v_i_boxed_1970_; lean_object* v_res_1971_; 
v_sz_boxed_1969_ = lean_unbox_usize(v_sz_1966_);
lean_dec(v_sz_1966_);
v_i_boxed_1970_ = lean_unbox_usize(v_i_1967_);
lean_dec(v_i_1967_);
v_res_1971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_boxed_1969_, v_i_boxed_1970_, v_bs_1968_);
return v_res_1971_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(lean_object* v_module_1975_, lean_object* v_decls_1976_, lean_object* v_f_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1980_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__0));
v___x_1981_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__1));
lean_inc_ref(v_decls_1976_);
v___x_1982_ = lean_array_to_list(v_decls_1976_);
v___x_1983_ = l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0(v___x_1982_);
v___x_1984_ = lean_string_append(v___x_1981_, v___x_1983_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = lean_string_append(v___x_1980_, v___x_1984_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___closed__2));
v___x_1987_ = lean_string_append(v___x_1985_, v___x_1986_);
v___x_1988_ = 1;
lean_inc(v_module_1975_);
v___x_1989_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1975_, v___x_1988_);
v___x_1990_ = lean_string_append(v___x_1987_, v___x_1989_);
lean_dec_ref(v___x_1989_);
v___x_1991_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; size_t v_sz_1998_; size_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec_ref_known(v___x_1991_, 1);
v___x_1992_ = l_Lean_Name_toString(v_module_1975_, v___x_1988_);
v___x_1993_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_buildSandboxArgs___closed__8));
v___x_1994_ = lean_unsigned_to_nat(2u);
v___x_1995_ = lean_mk_empty_array_with_capacity(v___x_1994_);
v___x_1996_ = lean_array_push(v___x_1995_, v___x_1992_);
v___x_1997_ = lean_array_push(v___x_1996_, v___x_1993_);
v_sz_1998_ = lean_array_size(v_decls_1976_);
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__1(v_sz_1998_, v___x_1999_, v_decls_1976_);
v___x_2001_ = l_Array_append___redArg(v___x_1997_, v___x_2000_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = l___private_Lake_CLI_Check_0__Lake_Check_withRunExporter___redArg(v___x_2001_, v_f_1977_, v_a_1978_);
return v___x_2002_;
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_f_1977_);
lean_dec_ref(v_decls_1976_);
lean_dec(v_module_1975_);
v_a_2003_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1991_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1991_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_module_1975_ = stack[0].m_obj;
lean_object* v_decls_1976_ = stack[1].m_obj;
lean_object* v_f_1977_ = stack[2].m_obj;
lean_object* v_a_1978_ = stack[3].m_obj;
lean_object* v_res_2011_;
v_res_2011_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_1975_, v_decls_1976_, v_f_1977_, v_a_1978_);
stack->m_obj
 = v_res_2011_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg___boxed(lean_object* v_module_2012_, lean_object* v_decls_2013_, lean_object* v_f_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_2012_, v_decls_2013_, v_f_2014_, v_a_2015_);
lean_dec_ref(v_a_2015_);
return v_res_2017_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_object* v_00_u03b1_2018_, lean_object* v_module_2019_, lean_object* v_decls_2020_, lean_object* v_f_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_2019_, v_decls_2020_, v_f_2021_, v_a_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport_0interp(lean_interpreter_value* stack)
{
lean_object* v_module_2019_ = stack[1].m_obj;
lean_object* v_decls_2020_ = stack[2].m_obj;
lean_object* v_f_2021_ = stack[3].m_obj;
lean_object* v_a_2022_ = stack[4].m_obj;
lean_object* v_res_2025_;
v_res_2025_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(lean_box(0), v_module_2019_, v_decls_2020_, v_f_2021_, v_a_2022_);
stack->m_obj
 = v_res_2025_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___boxed(lean_object* v_00_u03b1_2026_, lean_object* v_module_2027_, lean_object* v_decls_2028_, lean_object* v_f_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport(v_00_u03b1_2026_, v_module_2027_, v_decls_2028_, v_f_2029_, v_a_2030_);
lean_dec_ref(v_a_2030_);
return v_res_2032_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(uint8_t v_kind_2033_, lean_object* v_module_2034_, lean_object* v_decls_2035_, lean_object* v_f_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_moduleStore_2039_; lean_object* v___x_2040_; 
v_moduleStore_2039_ = lean_ctor_get(v_a_2037_, 17);
v___x_2040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__0___redArg(v_moduleStore_2039_, v_kind_2033_);
if (lean_obj_tag(v___x_2040_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2042_; 
lean_dec_ref(v_decls_2035_);
lean_dec(v_module_2034_);
v_val_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_val_2041_);
lean_dec_ref_known(v___x_2040_, 1);
lean_inc_ref(v_a_2037_);
v___x_2042_ = lean_apply_3(v_f_2036_, v_val_2041_, v_a_2037_, lean_box(0));
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec(v___x_2040_);
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = lean_mk_empty_array_with_capacity(v___x_2043_);
lean_inc(v_module_2034_);
v___x_2045_ = lean_array_push(v___x_2044_, v_module_2034_);
v___x_2046_ = l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild(v___x_2045_, v_a_2037_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; 
lean_dec_ref_known(v___x_2046_, 1);
v___x_2047_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeExport___redArg(v_module_2034_, v_decls_2035_, v_f_2036_, v_a_2037_);
return v___x_2047_;
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_f_2036_);
lean_dec_ref(v_decls_2035_);
lean_dec(v_module_2034_);
v_a_2048_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2046_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2046_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_2033_ = stack[0].m_num;
lean_object* v_module_2034_ = stack[1].m_obj;
lean_object* v_decls_2035_ = stack[2].m_obj;
lean_object* v_f_2036_ = stack[3].m_obj;
lean_object* v_a_2037_ = stack[4].m_obj;
lean_object* v_res_2056_;
v_res_2056_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_2033_, v_module_2034_, v_decls_2035_, v_f_2036_, v_a_2037_);
stack->m_obj
 = v_res_2056_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg___boxed(lean_object* v_kind_2057_, lean_object* v_module_2058_, lean_object* v_decls_2059_, lean_object* v_f_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
uint8_t v_kind_boxed_2063_; lean_object* v_res_2064_; 
v_kind_boxed_2063_ = lean_unbox(v_kind_2057_);
v_res_2064_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_boxed_2063_, v_module_2058_, v_decls_2059_, v_f_2060_, v_a_2061_);
lean_dec_ref(v_a_2061_);
return v_res_2064_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_object* v_00_u03b1_2065_, uint8_t v_kind_2066_, lean_object* v_module_2067_, lean_object* v_decls_2068_, lean_object* v_f_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v_kind_2066_, v_module_2067_, v_decls_2068_, v_f_2069_, v_a_2070_);
return v___x_2072_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport_0interp(lean_interpreter_value* stack)
{
uint8_t v_kind_2066_ = stack[1].m_num;
lean_object* v_module_2067_ = stack[2].m_obj;
lean_object* v_decls_2068_ = stack[3].m_obj;
lean_object* v_f_2069_ = stack[4].m_obj;
lean_object* v_a_2070_ = stack[5].m_obj;
lean_object* v_res_2073_;
v_res_2073_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(lean_box(0), v_kind_2066_, v_module_2067_, v_decls_2068_, v_f_2069_, v_a_2070_);
stack->m_obj
 = v_res_2073_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_kind_2075_, lean_object* v_module_2076_, lean_object* v_decls_2077_, lean_object* v_f_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
uint8_t v_kind_boxed_2081_; lean_object* v_res_2082_; 
v_kind_boxed_2081_ = lean_unbox(v_kind_2075_);
v_res_2082_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport(v_00_u03b1_2074_, v_kind_boxed_2081_, v_module_2076_, v_decls_2077_, v_f_2078_, v_a_2079_);
lean_dec_ref(v_a_2079_);
return v_res_2082_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(lean_object* v_s_2083_, lean_object* v_a_2084_, uint8_t v_b_2085_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = 0;
switch(lean_obj_tag(v_a_2084_))
{
case 0:
{
lean_object* v_pos_2087_; lean_object* v_startInclusive_2088_; lean_object* v_endExclusive_2089_; lean_object* v___x_2090_; uint8_t v_decide_2091_; 
v_pos_2087_ = lean_ctor_get(v_a_2084_, 0);
lean_inc(v_pos_2087_);
lean_dec_ref_known(v_a_2084_, 1);
v_startInclusive_2088_ = lean_ctor_get(v_s_2083_, 1);
v_endExclusive_2089_ = lean_ctor_get(v_s_2083_, 2);
v___x_2090_ = lean_nat_sub(v_endExclusive_2089_, v_startInclusive_2088_);
v_decide_2091_ = lean_nat_dec_eq(v_pos_2087_, v___x_2090_);
lean_dec(v___x_2090_);
lean_dec(v_pos_2087_);
if (v_decide_2091_ == 0)
{
uint8_t v___x_2092_; 
v___x_2092_ = 1;
return v___x_2092_;
}
else
{
return v_decide_2091_;
}
}
case 1:
{
lean_object* v_pos_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2106_; 
v_pos_2093_ = lean_ctor_get(v_a_2084_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_a_2084_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2095_ = v_a_2084_;
v_isShared_2096_ = v_isSharedCheck_2106_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_pos_2093_);
lean_dec(v_a_2084_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2106_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_str_2097_; lean_object* v_startInclusive_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v_str_2097_ = lean_ctor_get(v_s_2083_, 0);
v_startInclusive_2098_ = lean_ctor_get(v_s_2083_, 1);
v___x_2099_ = lean_nat_add(v_startInclusive_2098_, v_pos_2093_);
lean_dec(v_pos_2093_);
v___x_2100_ = lean_string_utf8_next_fast(v_str_2097_, v___x_2099_);
lean_dec(v___x_2099_);
v___x_2101_ = lean_nat_sub(v___x_2100_, v_startInclusive_2098_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2101_);
v___x_2103_ = v___x_2095_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
v_a_2084_ = v___x_2103_;
v_b_2085_ = v___x_2086_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_2107_; lean_object* v_table_2108_; lean_object* v_stackPos_2109_; lean_object* v_needlePos_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2165_; 
v_needle_2107_ = lean_ctor_get(v_a_2084_, 0);
v_table_2108_ = lean_ctor_get(v_a_2084_, 1);
v_stackPos_2109_ = lean_ctor_get(v_a_2084_, 2);
v_needlePos_2110_ = lean_ctor_get(v_a_2084_, 3);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_a_2084_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2112_ = v_a_2084_;
v_isShared_2113_ = v_isSharedCheck_2165_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_needlePos_2110_);
lean_inc(v_stackPos_2109_);
lean_inc(v_table_2108_);
lean_inc(v_needle_2107_);
lean_dec(v_a_2084_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2165_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_str_2114_; lean_object* v_startInclusive_2115_; lean_object* v_endExclusive_2116_; lean_object* v_str_2117_; lean_object* v_startInclusive_2118_; lean_object* v_endExclusive_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_str_2114_ = lean_ctor_get(v_needle_2107_, 0);
v_startInclusive_2115_ = lean_ctor_get(v_needle_2107_, 1);
v_endExclusive_2116_ = lean_ctor_get(v_needle_2107_, 2);
v_str_2117_ = lean_ctor_get(v_s_2083_, 0);
v_startInclusive_2118_ = lean_ctor_get(v_s_2083_, 1);
v_endExclusive_2119_ = lean_ctor_get(v_s_2083_, 2);
v___x_2120_ = lean_nat_sub(v_stackPos_2109_, v_needlePos_2110_);
v___x_2121_ = lean_nat_sub(v_endExclusive_2116_, v_startInclusive_2115_);
v___x_2122_ = lean_nat_add(v___x_2120_, v___x_2121_);
v___x_2123_ = lean_nat_sub(v_endExclusive_2119_, v_startInclusive_2118_);
v___x_2124_ = lean_nat_dec_le(v___x_2122_, v___x_2123_);
lean_dec(v___x_2122_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
lean_dec(v___x_2121_);
lean_del_object(v___x_2112_);
lean_dec(v_needlePos_2110_);
lean_dec(v_stackPos_2109_);
lean_dec_ref(v_table_2108_);
lean_dec_ref(v_needle_2107_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_add(v___x_2120_, v___x_2125_);
lean_dec(v___x_2120_);
v___x_2127_ = lean_nat_dec_le(v___x_2126_, v___x_2123_);
lean_dec(v___x_2123_);
lean_dec(v___x_2126_);
if (v___x_2127_ == 0)
{
return v_b_2085_;
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_box(3);
v_a_2084_ = v___x_2128_;
v_b_2085_ = v___x_2086_;
goto _start;
}
}
else
{
lean_object* v___x_2130_; uint8_t v_stackByte_2131_; lean_object* v___x_2132_; uint8_t v_patByte_2133_; uint8_t v___x_2134_; 
lean_dec(v___x_2123_);
lean_dec(v___x_2120_);
v___x_2130_ = lean_nat_add(v_startInclusive_2118_, v_stackPos_2109_);
v_stackByte_2131_ = lean_string_get_byte_fast(v_str_2117_, v___x_2130_);
v___x_2132_ = lean_nat_add(v_startInclusive_2115_, v_needlePos_2110_);
v_patByte_2133_ = lean_string_get_byte_fast(v_str_2114_, v___x_2132_);
v___x_2134_ = lean_uint8_dec_eq(v_stackByte_2131_, v_patByte_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v_decide_2136_; 
lean_dec(v___x_2121_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v_decide_2136_ = lean_nat_dec_eq(v_needlePos_2110_, v___x_2135_);
if (v_decide_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_newNeedlePos_2139_; uint8_t v___x_2140_; 
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_sub(v_needlePos_2110_, v___x_2137_);
lean_dec(v_needlePos_2110_);
v_newNeedlePos_2139_ = lean_array_fget_borrowed(v_table_2108_, v___x_2138_);
lean_dec(v___x_2138_);
v___x_2140_ = lean_nat_dec_eq(v_newNeedlePos_2139_, v___x_2135_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2142_; 
lean_inc(v_newNeedlePos_2139_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 3, v_newNeedlePos_2139_);
v___x_2142_ = v___x_2112_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_needle_2107_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_table_2108_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_stackPos_2109_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_newNeedlePos_2139_);
v___x_2142_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
v_a_2084_ = v___x_2142_;
v_b_2085_ = v___x_2086_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_2145_; lean_object* v___x_2147_; 
v_nextStackPos_2145_ = l_String_Slice_posGE___redArg(v_s_2083_, v_stackPos_2109_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 3, v___x_2135_);
lean_ctor_set(v___x_2112_, 2, v_nextStackPos_2145_);
v___x_2147_ = v___x_2112_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_needle_2107_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_table_2108_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_nextStackPos_2145_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v___x_2135_);
v___x_2147_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v_a_2084_ = v___x_2147_;
v_b_2085_ = v___x_2086_;
goto _start;
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_nextStackPos_2152_; lean_object* v___x_2154_; 
lean_dec(v_needlePos_2110_);
v___x_2150_ = lean_unsigned_to_nat(1u);
v___x_2151_ = lean_nat_add(v_stackPos_2109_, v___x_2150_);
lean_dec(v_stackPos_2109_);
v_nextStackPos_2152_ = l_String_Slice_posGE___redArg(v_s_2083_, v___x_2151_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 3, v___x_2135_);
lean_ctor_set(v___x_2112_, 2, v_nextStackPos_2152_);
v___x_2154_ = v___x_2112_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_needle_2107_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_table_2108_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_nextStackPos_2152_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v___x_2135_);
v___x_2154_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
v_a_2084_ = v___x_2154_;
v_b_2085_ = v___x_2086_;
goto _start;
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v_nextNeedlePos_2158_; uint8_t v_decide_2159_; 
v___x_2157_ = lean_unsigned_to_nat(1u);
v_nextNeedlePos_2158_ = lean_nat_add(v_needlePos_2110_, v___x_2157_);
lean_dec(v_needlePos_2110_);
v_decide_2159_ = lean_nat_dec_eq(v_nextNeedlePos_2158_, v___x_2121_);
lean_dec(v___x_2121_);
if (v_decide_2159_ == 0)
{
lean_object* v_nextStackPos_2160_; lean_object* v___x_2162_; 
v_nextStackPos_2160_ = lean_nat_add(v_stackPos_2109_, v___x_2157_);
lean_dec(v_stackPos_2109_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 3, v_nextNeedlePos_2158_);
lean_ctor_set(v___x_2112_, 2, v_nextStackPos_2160_);
v___x_2162_ = v___x_2112_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_needle_2107_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_table_2108_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_nextStackPos_2160_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_nextNeedlePos_2158_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_a_2084_ = v___x_2162_;
goto _start;
}
}
else
{
lean_dec(v_nextNeedlePos_2158_);
lean_del_object(v___x_2112_);
lean_dec(v_stackPos_2109_);
lean_dec_ref(v_table_2108_);
lean_dec_ref(v_needle_2107_);
return v_decide_2159_;
}
}
}
}
}
default: 
{
return v_b_2085_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2083_ = stack[0].m_obj;
lean_object* v_a_2084_ = stack[1].m_obj;
uint8_t v_b_2085_ = stack[2].m_num;
uint8_t v_res_2166_;
v_res_2166_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2083_, v_a_2084_, v_b_2085_);
stack->m_num = v_res_2166_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg___boxed(lean_object* v_s_2167_, lean_object* v_a_2168_, lean_object* v_b_2169_){
_start:
{
uint8_t v_b_boxed_2170_; uint8_t v_res_2171_; lean_object* v_r_2172_; 
v_b_boxed_2170_ = lean_unbox(v_b_2169_);
v_res_2171_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2167_, v_a_2168_, v_b_boxed_2170_);
lean_dec_ref(v_s_2167_);
v_r_2172_ = lean_box(v_res_2171_);
return v_r_2172_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1));
v___x_2179_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_2178_);
return v___x_2179_;
}
}
static lean_object* _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__2);
v___x_2182_ = ((lean_object*)(l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__1));
v___x_2183_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
lean_ctor_set(v___x_2183_, 2, v___x_2180_);
lean_ctor_set(v___x_2183_, 3, v___x_2180_);
return v___x_2183_;
}
}
uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(lean_object* v_s_2184_){
_start:
{
lean_object* v___x_2185_; uint8_t v___x_2186_; uint8_t v___x_2187_; 
v___x_2185_ = lean_obj_once(&l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3, &l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3_once, _init_l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___closed__3);
v___x_2186_ = 0;
v___x_2187_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2184_, v___x_2185_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2184_ = stack[0].m_obj;
uint8_t v_res_2188_;
v_res_2188_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_2184_);
stack->m_num = v_res_2188_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0___boxed(lean_object* v_s_2189_){
_start:
{
uint8_t v_res_2190_; lean_object* v_r_2191_; 
v_res_2190_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v_s_2189_);
lean_dec_ref(v_s_2189_);
v_r_2191_ = lean_box(v_res_2190_);
return v_r_2191_;
}
}
uint8_t l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(lean_object* v_kernelName_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = lean_string_utf8_byte_size(v_kernelName_2192_);
v___x_2195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2195_, 0, v_kernelName_2192_);
lean_ctor_set(v___x_2195_, 1, v___x_2193_);
lean_ctor_set(v___x_2195_, 2, v___x_2194_);
v___x_2196_ = l_String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0(v___x_2195_);
lean_dec_ref_known(v___x_2195_, 3);
return v___x_2196_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_0interp(lean_interpreter_value* stack)
{
lean_object* v_kernelName_2192_ = stack[0].m_obj;
uint8_t v_res_2197_;
v_res_2197_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2192_);
stack->m_num = v_res_2197_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel___boxed(lean_object* v_kernelName_2198_){
_start:
{
uint8_t v_res_2199_; lean_object* v_r_2200_; 
v_res_2199_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2198_);
v_r_2200_ = lean_box(v_res_2199_);
return v_r_2200_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(lean_object* v_s_2201_, lean_object* v_inst_2202_, lean_object* v_R_2203_, lean_object* v_a_2204_, uint8_t v_b_2205_, lean_object* v_c_2206_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___redArg(v_s_2201_, v_a_2204_, v_b_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2201_ = stack[0].m_obj;
lean_object* v_a_2204_ = stack[3].m_obj;
uint8_t v_b_2205_ = stack[4].m_num;
uint8_t v_res_2208_;
v_res_2208_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_2201_, lean_box(0), lean_box(0), v_a_2204_, v_b_2205_, lean_box(0));
stack->m_num = v_res_2208_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0___boxed(lean_object* v_s_2209_, lean_object* v_inst_2210_, lean_object* v_R_2211_, lean_object* v_a_2212_, lean_object* v_b_2213_, lean_object* v_c_2214_){
_start:
{
uint8_t v_b_boxed_2215_; uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_b_boxed_2215_ = lean_unbox(v_b_2213_);
v_res_2216_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel_spec__0_spec__0(v_s_2209_, v_inst_2210_, v_R_2211_, v_a_2212_, v_b_boxed_2215_, v_c_2214_);
lean_dec_ref(v_s_2209_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(lean_object* v_a_2218_, lean_object* v_b_2219_){
_start:
{
lean_object* v_array_2220_; lean_object* v_start_2221_; lean_object* v_stop_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2235_; 
v_array_2220_ = lean_ctor_get(v_a_2218_, 0);
v_start_2221_ = lean_ctor_get(v_a_2218_, 1);
v_stop_2222_ = lean_ctor_get(v_a_2218_, 2);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_a_2218_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2224_ = v_a_2218_;
v_isShared_2225_ = v_isSharedCheck_2235_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_stop_2222_);
lean_inc(v_start_2221_);
lean_inc(v_array_2220_);
lean_dec(v_a_2218_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2235_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_nat_dec_lt(v_start_2221_, v_stop_2222_);
if (v___x_2226_ == 0)
{
lean_del_object(v___x_2224_);
lean_dec(v_stop_2222_);
lean_dec(v_start_2221_);
lean_dec_ref(v_array_2220_);
return v_b_2219_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_nat_add(v_start_2221_, v___x_2227_);
lean_inc_ref(v_array_2220_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 1, v___x_2228_);
v___x_2230_ = v___x_2224_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_array_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_stop_2222_);
v___x_2230_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_array_fget(v_array_2220_, v_start_2221_);
lean_dec(v_start_2221_);
lean_dec_ref(v_array_2220_);
v___x_2232_ = lean_array_push(v_b_2219_, v___x_2231_);
v_a_2218_ = v___x_2230_;
v_b_2219_ = v___x_2232_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(size_t v_sz_2236_, size_t v_i_2237_, lean_object* v_bs_2238_){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = lean_usize_dec_lt(v_i_2237_, v_sz_2236_);
if (v___x_2239_ == 0)
{
return v_bs_2238_;
}
else
{
lean_object* v_v_2240_; lean_object* v___x_2241_; lean_object* v_bs_x27_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v_v_2240_ = lean_array_uget(v_bs_2238_, v_i_2237_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v_bs_x27_2242_ = lean_array_uset(v_bs_2238_, v_i_2237_, v___x_2241_);
v___x_2243_ = l_Lean_Name_toString(v_v_2240_, v___x_2239_);
v___x_2244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
v___x_2245_ = ((size_t)1ULL);
v___x_2246_ = lean_usize_add(v_i_2237_, v___x_2245_);
v___x_2247_ = lean_array_uset(v_bs_x27_2242_, v_i_2237_, v___x_2244_);
v_i_2237_ = v___x_2246_;
v_bs_2238_ = v___x_2247_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2236_ = stack[0].m_num;
size_t v_i_2237_ = stack[1].m_num;
lean_object* v_bs_2238_ = stack[2].m_obj;
lean_object* v_res_2249_;
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_2236_, v_i_2237_, v_bs_2238_);
stack->m_obj
 = v_res_2249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0___boxed(lean_object* v_sz_2250_, lean_object* v_i_2251_, lean_object* v_bs_2252_){
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2250_);
lean_dec(v_sz_2250_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2251_);
lean_dec(v_i_2251_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_boxed_2253_, v_i_boxed_2254_, v_bs_2252_);
return v_res_2255_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = lean_unsigned_to_nat(4u);
v___x_2280_ = l_Lean_JsonNumber_fromNat(v___x_2279_);
return v___x_2280_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__15);
v___x_2282_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
return v___x_2282_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__16);
v___x_2284_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__14));
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
lean_ctor_set(v___x_2285_, 1, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__24));
v___x_2303_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__17);
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__25);
v___x_2306_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__13));
v___x_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___x_2305_);
return v___x_2307_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(lean_object* v_kernelName_2308_, lean_object* v_solutionPath_2309_, lean_object* v___x_2310_, lean_object* v_kernelCommand_2311_, lean_object* v_configHandle_2312_, lean_object* v_configPath_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_a_2317_; lean_object* v_legalAxioms_2344_; uint8_t v___x_2345_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v_kernelArgs_2419_; lean_object* v___y_2420_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; size_t v_sz_2431_; size_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_legalAxioms_2344_ = lean_ctor_get(v___y_2314_, 5);
v___x_2345_ = 0;
v___x_2426_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__9));
v___x_2427_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__10));
lean_inc_ref(v_solutionPath_2309_);
v___x_2428_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_solutionPath_2309_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v_sz_2431_ = lean_array_size(v_legalAxioms_2344_);
v___x_2432_ = ((size_t)0ULL);
lean_inc_ref(v_legalAxioms_2344_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__0(v_sz_2431_, v___x_2432_, v_legalAxioms_2344_);
v___x_2434_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2430_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26, &l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__26);
v___x_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2429_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2426_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = l_Lean_Json_mkObj(v___x_2439_);
lean_dec_ref_known(v___x_2439_, 2);
v___x_2441_ = l_Lean_Json_compress(v___x_2440_);
v___x_2442_ = lean_io_prim_handle_put_str(v_configHandle_2312_, v___x_2441_);
lean_dec_ref(v___x_2441_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref_known(v___x_2442_, 1);
v___x_2443_ = lean_io_prim_handle_flush(v_configHandle_2312_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
lean_dec_ref_known(v___x_2443_, 1);
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_array_get_size(v_kernelCommand_2311_);
lean_inc_ref(v_kernelCommand_2311_);
v___x_2446_ = l_Array_toSubarray___redArg(v_kernelCommand_2311_, v___x_2444_, v___x_2445_);
v___x_2447_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___x_2448_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v___x_2446_, v___x_2447_);
lean_inc_ref(v_kernelName_2308_);
v___x_2449_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_isNanodaKernel(v_kernelName_2308_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
lean_inc_ref(v_solutionPath_2309_);
v___x_2450_ = lean_array_push(v___x_2448_, v_solutionPath_2309_);
v_kernelArgs_2419_ = v___x_2450_;
v___y_2420_ = v___y_2314_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2451_; 
lean_inc_ref(v_configPath_2313_);
v___x_2451_ = lean_array_push(v___x_2448_, v_configPath_2313_);
v_kernelArgs_2419_ = v___x_2451_;
v___y_2420_ = v___y_2314_;
goto v___jp_2418_;
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v_configPath_2313_);
lean_dec_ref(v_kernelCommand_2311_);
lean_dec_ref(v_solutionPath_2309_);
lean_dec_ref(v_kernelName_2308_);
v_a_2452_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2443_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2443_);
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
lean_dec_ref(v_configPath_2313_);
lean_dec_ref(v_kernelCommand_2311_);
lean_dec_ref(v_solutionPath_2309_);
lean_dec_ref(v_kernelName_2308_);
v_a_2460_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2442_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2442_);
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
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2318_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__0));
v___x_2319_ = lean_string_append(v___x_2318_, v_kernelName_2308_);
lean_dec_ref(v_kernelName_2308_);
v___x_2320_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__1));
lean_inc_ref(v___x_2319_);
v___x_2321_ = lean_string_append(v___x_2319_, v___x_2320_);
v___x_2322_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2334_; 
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___x_2322_, 0);
lean_dec(v_unused_2335_);
v___x_2324_ = v___x_2322_;
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
else
{
lean_dec(v___x_2322_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2326_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__2));
v___x_2327_ = lean_string_append(v___x_2319_, v___x_2326_);
v___x_2328_ = lean_io_error_to_string(v_a_2317_);
v___x_2329_ = lean_string_append(v___x_2327_, v___x_2328_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2330_);
v___x_2332_ = v___x_2324_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___x_2319_);
lean_dec(v_a_2317_);
v_a_2336_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2322_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2322_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
v___jp_2346_:
{
lean_object* v_leanPrefix_2351_; lean_object* v___x_2352_; 
v_leanPrefix_2351_ = lean_ctor_get(v___y_2349_, 6);
v___x_2352_ = lean_uv_os_tmpdir();
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__4));
v___x_2355_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__12));
v___x_2356_ = lean_unsigned_to_nat(4u);
v___x_2357_ = lean_mk_empty_array_with_capacity(v___x_2356_);
v___x_2358_ = lean_array_push(v___x_2357_, v_configPath_2313_);
v___x_2359_ = lean_array_push(v___x_2358_, v_solutionPath_2309_);
lean_inc_ref(v___y_2350_);
v___x_2360_ = lean_array_push(v___x_2359_, v___y_2350_);
lean_inc_ref(v_leanPrefix_2351_);
v___x_2361_ = lean_array_push(v___x_2360_, v_leanPrefix_2351_);
v___x_2362_ = lean_mk_empty_array_with_capacity(v___y_2348_);
v___x_2363_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_forbiddenPaths));
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_a_2353_);
v___x_2365_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2365_, 0, v___y_2350_);
lean_ctor_set(v___x_2365_, 1, v___y_2347_);
lean_ctor_set(v___x_2365_, 2, v___x_2354_);
lean_ctor_set(v___x_2365_, 3, v___x_2355_);
lean_ctor_set(v___x_2365_, 4, v___x_2361_);
lean_ctor_set(v___x_2365_, 5, v___x_2362_);
lean_ctor_set(v___x_2365_, 6, v___x_2363_);
lean_ctor_set(v___x_2365_, 7, v___x_2364_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*8, v___x_2345_);
v___x_2366_ = l___private_Lake_CLI_Check_0__Lake_Check_runSandBoxedExitCode(v___x_2365_, v___y_2349_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2408_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2408_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2408_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
uint32_t v___x_2371_; uint32_t v___x_2372_; uint8_t v___x_2373_; 
v___x_2371_ = 0;
v___x_2372_ = lean_unbox_uint32(v_a_2367_);
v___x_2373_ = lean_uint32_dec_eq(v___x_2372_, v___x_2371_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__5));
lean_inc_ref(v_kernelName_2308_);
v___x_2375_ = lean_string_append(v_kernelName_2308_, v___x_2374_);
v___x_2376_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2375_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2392_; 
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v___x_2376_, 0);
lean_dec(v_unused_2393_);
v___x_2378_ = v___x_2376_;
v_isShared_2379_ = v_isSharedCheck_2392_;
goto v_resetjp_2377_;
}
else
{
lean_dec(v___x_2376_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2392_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; uint32_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2380_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__6));
v___x_2381_ = lean_string_append(v_kernelName_2308_, v___x_2380_);
v___x_2382_ = lean_unbox_uint32(v_a_2367_);
lean_dec(v_a_2367_);
v___x_2383_ = lean_uint32_to_nat(v___x_2382_);
v___x_2384_ = l_Nat_reprFast(v___x_2383_);
v___x_2385_ = lean_string_append(v___x_2381_, v___x_2384_);
lean_dec_ref(v___x_2384_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set_tag(v___x_2369_, 1);
lean_ctor_set(v___x_2369_, 0, v___x_2385_);
v___x_2387_ = v___x_2369_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2387_);
v___x_2389_ = v___x_2378_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2394_; 
lean_del_object(v___x_2369_);
lean_dec(v_a_2367_);
v_a_2394_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2376_, 1);
v_a_2317_ = v_a_2394_;
goto v___jp_2316_;
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_del_object(v___x_2369_);
lean_dec(v_a_2367_);
v___x_2395_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__7));
lean_inc_ref(v_kernelName_2308_);
v___x_2396_ = lean_string_append(v_kernelName_2308_, v___x_2395_);
v___x_2397_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2396_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v_kernelName_2308_);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2397_, 0);
lean_dec(v_unused_2406_);
v___x_2399_ = v___x_2397_;
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
else
{
lean_dec(v___x_2397_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = lean_box(0);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2401_);
v___x_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
else
{
lean_object* v_a_2407_; 
v_a_2407_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2397_, 1);
v_a_2317_ = v_a_2407_;
goto v___jp_2316_;
}
}
}
}
else
{
lean_object* v_a_2409_; 
v_a_2409_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2366_, 1);
v_a_2317_ = v_a_2409_;
goto v___jp_2316_;
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v___y_2350_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_configPath_2313_);
lean_dec_ref(v_solutionPath_2309_);
lean_dec_ref(v_kernelName_2308_);
v_a_2410_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2352_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2352_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
v___jp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v_a_2424_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_array_get(v___x_2310_, v_kernelCommand_2311_, v___x_2421_);
lean_dec_ref(v_kernelCommand_2311_);
lean_inc(v___x_2422_);
v___x_2423_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_2422_);
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref(v___x_2423_);
if (lean_obj_tag(v_a_2424_) == 0)
{
v___y_2347_ = v_kernelArgs_2419_;
v___y_2348_ = v___x_2421_;
v___y_2349_ = v___y_2420_;
v___y_2350_ = v___x_2422_;
goto v___jp_2346_;
}
else
{
lean_object* v_val_2425_; 
lean_dec(v___x_2422_);
v_val_2425_ = lean_ctor_get(v_a_2424_, 0);
lean_inc(v_val_2425_);
lean_dec_ref_known(v_a_2424_, 1);
v___y_2347_ = v_kernelArgs_2419_;
v___y_2348_ = v___x_2421_;
v___y_2349_ = v___y_2420_;
v___y_2350_ = v_val_2425_;
goto v___jp_2346_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kernelName_2308_ = stack[0].m_obj;
lean_object* v_solutionPath_2309_ = stack[1].m_obj;
lean_object* v___x_2310_ = stack[2].m_obj;
lean_object* v_kernelCommand_2311_ = stack[3].m_obj;
lean_object* v_configHandle_2312_ = stack[4].m_obj;
lean_object* v_configPath_2313_ = stack[5].m_obj;
lean_object* v___y_2314_ = stack[6].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_kernelName_2308_, v_solutionPath_2309_, v___x_2310_, v_kernelCommand_2311_, v_configHandle_2312_, v_configPath_2313_, v___y_2314_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed(lean_object* v_kernelName_2469_, lean_object* v_solutionPath_2470_, lean_object* v___x_2471_, lean_object* v_kernelCommand_2472_, lean_object* v_configHandle_2473_, lean_object* v_configPath_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0(v_kernelName_2469_, v_solutionPath_2470_, v___x_2471_, v_kernelCommand_2472_, v_configHandle_2473_, v_configPath_2474_, v___y_2475_);
lean_dec_ref(v___y_2475_);
lean_dec(v_configHandle_2473_);
lean_dec_ref(v___x_2471_);
return v_res_2477_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(lean_object* v_kernelName_2480_, lean_object* v_kernelCommand_2481_, lean_object* v_solutionPath_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v___x_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2485_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
lean_inc_ref(v_kernelName_2480_);
v___f_2486_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2486_, 0, v_kernelName_2480_);
lean_closure_set(v___f_2486_, 1, v_solutionPath_2482_);
lean_closure_set(v___f_2486_, 2, v___x_2485_);
lean_closure_set(v___f_2486_, 3, v_kernelCommand_2481_);
v___x_2487_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__0));
v___x_2488_ = lean_string_append(v___x_2487_, v_kernelName_2480_);
lean_dec_ref(v_kernelName_2480_);
v___x_2489_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___closed__1));
v___x_2490_ = lean_string_append(v___x_2488_, v___x_2489_);
v___x_2491_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_2490_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; 
lean_dec_ref_known(v___x_2491_, 1);
v___x_2492_ = l_IO_FS_withTempFile___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport_spec__1___redArg(v___f_2486_, v_a_2483_);
return v___x_2492_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v___f_2486_);
v_a_2493_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2491_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2491_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_0interp(lean_interpreter_value* stack)
{
lean_object* v_kernelName_2480_ = stack[0].m_obj;
lean_object* v_kernelCommand_2481_ = stack[1].m_obj;
lean_object* v_solutionPath_2482_ = stack[2].m_obj;
lean_object* v_a_2483_ = stack[3].m_obj;
lean_object* v_res_2501_;
v_res_2501_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_2480_, v_kernelCommand_2481_, v_solutionPath_2482_, v_a_2483_);
stack->m_obj
 = v_res_2501_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___boxed(lean_object* v_kernelName_2502_, lean_object* v_kernelCommand_2503_, lean_object* v_solutionPath_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_kernelName_2502_, v_kernelCommand_2503_, v_solutionPath_2504_, v_a_2505_);
lean_dec_ref(v_a_2505_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1(lean_object* v_inst_2508_, lean_object* v_R_2509_, lean_object* v_a_2510_, lean_object* v_b_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_CLI_Check_0__Lake_Check_runExternalKernel_spec__1___redArg(v_a_2510_, v_b_2511_);
return v___x_2512_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(lean_object* v_solutionPath_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_whichLeanChecker_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_whichLeanChecker_2519_ = lean_ctor_get(v_a_2517_, 13);
v___x_2520_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_2521_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_2522_ = lean_unsigned_to_nat(3u);
v___x_2523_ = lean_mk_empty_array_with_capacity(v___x_2522_);
lean_inc_ref(v_whichLeanChecker_2519_);
v___x_2524_ = lean_array_push(v___x_2523_, v_whichLeanChecker_2519_);
v___x_2525_ = lean_array_push(v___x_2524_, v___x_2520_);
v___x_2526_ = lean_array_push(v___x_2525_, v___x_2521_);
v___x_2527_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__2));
v___x_2528_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v___x_2527_, v___x_2526_, v_solutionPath_2516_, v_a_2517_);
return v___x_2528_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel_0interp(lean_interpreter_value* stack)
{
lean_object* v_solutionPath_2516_ = stack[0].m_obj;
lean_object* v_a_2517_ = stack[1].m_obj;
lean_object* v_res_2529_;
v_res_2529_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionPath_2516_, v_a_2517_);
stack->m_obj
 = v_res_2529_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___boxed(lean_object* v_solutionPath_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_solutionPath_2530_, v_a_2531_);
lean_dec_ref(v_a_2531_);
return v_res_2533_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(lean_object* v_exportPath_2534_, lean_object* v_as_2535_, size_t v_sz_2536_, size_t v_i_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_a_2542_; uint8_t v___x_2546_; 
v___x_2546_ = lean_usize_dec_lt(v_i_2537_, v_sz_2536_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
lean_dec_ref(v_exportPath_2534_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_b_2538_);
return v___x_2547_;
}
else
{
lean_object* v_a_2548_; lean_object* v_fst_2549_; lean_object* v_snd_2550_; lean_object* v___x_2551_; 
v_a_2548_ = lean_array_uget_borrowed(v_as_2535_, v_i_2537_);
v_fst_2549_ = lean_ctor_get(v_a_2548_, 0);
v_snd_2550_ = lean_ctor_get(v_a_2548_, 1);
lean_inc_ref(v_exportPath_2534_);
lean_inc(v_snd_2550_);
lean_inc(v_fst_2549_);
v___x_2551_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_fst_2549_, v_snd_2550_, v_exportPath_2534_, v___y_2539_);
if (lean_obj_tag(v___x_2551_) == 0)
{
if (lean_obj_tag(v_b_2538_) == 0)
{
lean_object* v_a_2552_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v_a_2542_ = v_a_2552_;
goto v___jp_2541_;
}
else
{
lean_dec_ref_known(v___x_2551_, 1);
v_a_2542_ = v_b_2538_;
goto v___jp_2541_;
}
}
else
{
lean_dec(v_b_2538_);
lean_dec_ref(v_exportPath_2534_);
return v___x_2551_;
}
}
v___jp_2541_:
{
size_t v___x_2543_; size_t v___x_2544_; 
v___x_2543_ = ((size_t)1ULL);
v___x_2544_ = lean_usize_add(v_i_2537_, v___x_2543_);
v_i_2537_ = v___x_2544_;
v_b_2538_ = v_a_2542_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_exportPath_2534_ = stack[0].m_obj;
lean_object* v_as_2535_ = stack[1].m_obj;
size_t v_sz_2536_ = stack[2].m_num;
size_t v_i_2537_ = stack[3].m_num;
lean_object* v_b_2538_ = stack[4].m_obj;
lean_object* v___y_2539_ = stack[5].m_obj;
lean_object* v_res_2553_;
v_res_2553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2534_, v_as_2535_, v_sz_2536_, v_i_2537_, v_b_2538_, v___y_2539_);
stack->m_obj
 = v_res_2553_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0___boxed(lean_object* v_exportPath_2554_, lean_object* v_as_2555_, lean_object* v_sz_2556_, lean_object* v_i_2557_, lean_object* v_b_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
size_t v_sz_boxed_2561_; size_t v_i_boxed_2562_; lean_object* v_res_2563_; 
v_sz_boxed_2561_ = lean_unbox_usize(v_sz_2556_);
lean_dec(v_sz_2556_);
v_i_boxed_2562_ = lean_unbox_usize(v_i_2557_);
lean_dec(v_i_2557_);
v_res_2563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2554_, v_as_2555_, v_sz_boxed_2561_, v_i_boxed_2562_, v_b_2558_, v___y_2559_);
lean_dec_ref(v___y_2559_);
lean_dec_ref(v_as_2555_);
return v_res_2563_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(lean_object* v_exportPath_2564_, lean_object* v_init_2565_, lean_object* v_x_2566_, lean_object* v___y_2567_){
_start:
{
if (lean_obj_tag(v_x_2566_) == 0)
{
lean_object* v_k_2569_; lean_object* v_v_2570_; lean_object* v_l_2571_; lean_object* v_r_2572_; lean_object* v___x_2573_; 
v_k_2569_ = lean_ctor_get(v_x_2566_, 1);
lean_inc(v_k_2569_);
v_v_2570_ = lean_ctor_get(v_x_2566_, 2);
lean_inc(v_v_2570_);
v_l_2571_ = lean_ctor_get(v_x_2566_, 3);
lean_inc(v_l_2571_);
v_r_2572_ = lean_ctor_get(v_x_2566_, 4);
lean_inc(v_r_2572_);
lean_dec_ref_known(v_x_2566_, 5);
lean_inc_ref(v_exportPath_2564_);
v___x_2573_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2564_, v_init_2565_, v_l_2571_, v___y_2567_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v_a_2575_; lean_object* v___x_2576_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v_a_2575_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_a_2575_);
lean_dec(v_a_2574_);
lean_inc_ref(v_exportPath_2564_);
v___x_2576_ = l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel(v_k_2569_, v_v_2570_, v_exportPath_2564_, v___y_2567_);
if (lean_obj_tag(v___x_2576_) == 0)
{
if (lean_obj_tag(v_a_2575_) == 0)
{
lean_object* v_a_2577_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v_init_2565_ = v_a_2577_;
v_x_2566_ = v_r_2572_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_2576_, 1);
v_init_2565_ = v_a_2575_;
v_x_2566_ = v_r_2572_;
goto _start;
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_a_2575_);
lean_dec(v_r_2572_);
lean_dec_ref(v_exportPath_2564_);
v_a_2580_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2576_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2576_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_dec(v_r_2572_);
lean_dec(v_v_2570_);
lean_dec(v_k_2569_);
lean_dec_ref(v_exportPath_2564_);
return v___x_2573_;
}
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec_ref(v_exportPath_2564_);
v___x_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_init_2565_);
v___x_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
return v___x_2589_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_exportPath_2564_ = stack[0].m_obj;
lean_object* v_init_2565_ = stack[1].m_obj;
lean_object* v_x_2566_ = stack[2].m_obj;
lean_object* v___y_2567_ = stack[3].m_obj;
lean_object* v_res_2590_;
v_res_2590_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2564_, v_init_2565_, v_x_2566_, v___y_2567_);
stack->m_obj
 = v_res_2590_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1___boxed(lean_object* v_exportPath_2591_, lean_object* v_init_2592_, lean_object* v_x_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2591_, v_init_2592_, v_x_2593_, v___y_2594_);
lean_dec_ref(v___y_2594_);
return v_res_2596_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels(lean_object* v_exportPath_2597_, lean_object* v_a_2598_){
_start:
{
lean_object* v_val_2601_; lean_object* v_externalKernels_2604_; lean_object* v_bundledKernels_2605_; lean_object* v_a_2607_; lean_object* v_result_2640_; lean_object* v___x_2641_; 
v_externalKernels_2604_ = lean_ctor_get(v_a_2598_, 15);
v_bundledKernels_2605_ = lean_ctor_get(v_a_2598_, 16);
v_result_2640_ = lean_box(0);
lean_inc(v_externalKernels_2604_);
lean_inc_ref(v_exportPath_2597_);
v___x_2641_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__1(v_exportPath_2597_, v_result_2640_, v_externalKernels_2604_, v_a_2598_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v_a_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v_a_2643_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_a_2643_);
lean_dec(v_a_2642_);
v_a_2607_ = v_a_2643_;
goto v___jp_2606_;
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec_ref(v_exportPath_2597_);
v_a_2644_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2641_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2641_);
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
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_mk_io_user_error(v_val_2601_);
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
v___jp_2606_:
{
size_t v_sz_2608_; size_t v___x_2609_; lean_object* v___x_2610_; 
v_sz_2608_ = lean_array_size(v_bundledKernels_2605_);
v___x_2609_ = ((size_t)0ULL);
lean_inc_ref(v_exportPath_2597_);
v___x_2610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_runKernels_spec__0(v_exportPath_2597_, v_bundledKernels_2605_, v_sz_2608_, v___x_2609_, v_a_2607_, v_a_2598_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel(v_exportPath_2597_, v_a_2598_);
if (lean_obj_tag(v___x_2612_) == 0)
{
if (lean_obj_tag(v_a_2611_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2622_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2622_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2622_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
if (lean_obj_tag(v_a_2613_) == 1)
{
lean_object* v_val_2617_; 
lean_del_object(v___x_2615_);
v_val_2617_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v_a_2613_, 1);
v_val_2601_ = v_val_2617_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
lean_dec(v_a_2613_);
v___x_2618_ = lean_box(0);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2618_);
v___x_2620_ = v___x_2615_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v_val_2623_; 
lean_dec_ref_known(v___x_2612_, 1);
v_val_2623_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v_a_2611_, 1);
v_val_2601_ = v_val_2623_;
goto v___jp_2600_;
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_a_2611_);
v_a_2624_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2612_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2612_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_exportPath_2597_);
v_a_2632_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2610_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2610_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_runKernels_0interp(lean_interpreter_value* stack)
{
lean_object* v_exportPath_2597_ = stack[0].m_obj;
lean_object* v_a_2598_ = stack[1].m_obj;
lean_object* v_res_2652_;
v_res_2652_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_2597_, v_a_2598_);
stack->m_obj
 = v_res_2652_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_runKernels___boxed(lean_object* v_exportPath_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_2653_, v_a_2654_);
lean_dec_ref(v_a_2654_);
return v_res_2656_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg(){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___closed__52));
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2809_;
v_res_2809_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
stack->m_obj
 = v_res_2809_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg___boxed(lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v_res_2811_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
return v___x_2814_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2812_ = stack[0].m_obj;
lean_object* v_res_2815_;
v_res_2815_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_2812_);
stack->m_obj
 = v_res_2815_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___boxed(lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets(v_a_2816_);
lean_dec_ref(v_a_2816_);
return v_res_2818_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(lean_object* v_a_2819_, lean_object* v_as_2820_, size_t v_i_2821_, size_t v_stop_2822_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = lean_usize_dec_eq(v_i_2821_, v_stop_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = lean_array_uget_borrowed(v_as_2820_, v_i_2821_);
v___x_2825_ = lean_name_eq(v_a_2819_, v___x_2824_);
if (v___x_2825_ == 0)
{
size_t v___x_2826_; size_t v___x_2827_; 
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2821_, v___x_2826_);
v_i_2821_ = v___x_2827_;
goto _start;
}
else
{
return v___x_2825_;
}
}
else
{
uint8_t v___x_2829_; 
v___x_2829_ = 0;
return v___x_2829_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2819_ = stack[0].m_obj;
lean_object* v_as_2820_ = stack[1].m_obj;
size_t v_i_2821_ = stack[2].m_num;
size_t v_stop_2822_ = stack[3].m_num;
uint8_t v_res_2830_;
v_res_2830_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2819_, v_as_2820_, v_i_2821_, v_stop_2822_);
stack->m_num = v_res_2830_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0___boxed(lean_object* v_a_2831_, lean_object* v_as_2832_, lean_object* v_i_2833_, lean_object* v_stop_2834_){
_start:
{
size_t v_i_boxed_2835_; size_t v_stop_boxed_2836_; uint8_t v_res_2837_; lean_object* v_r_2838_; 
v_i_boxed_2835_ = lean_unbox_usize(v_i_2833_);
lean_dec(v_i_2833_);
v_stop_boxed_2836_ = lean_unbox_usize(v_stop_2834_);
lean_dec(v_stop_2834_);
v_res_2837_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2831_, v_as_2832_, v_i_boxed_2835_, v_stop_boxed_2836_);
lean_dec_ref(v_as_2832_);
lean_dec(v_a_2831_);
v_r_2838_ = lean_box(v_res_2837_);
return v_r_2838_;
}
}
uint8_t l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(lean_object* v_as_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2841_ = lean_unsigned_to_nat(0u);
v___x_2842_ = lean_array_get_size(v_as_2839_);
v___x_2843_ = lean_nat_dec_lt(v___x_2841_, v___x_2842_);
if (v___x_2843_ == 0)
{
return v___x_2843_;
}
else
{
if (v___x_2843_ == 0)
{
return v___x_2843_;
}
else
{
size_t v___x_2844_; size_t v___x_2845_; uint8_t v___x_2846_; 
v___x_2844_ = ((size_t)0ULL);
v___x_2845_ = lean_usize_of_nat(v___x_2842_);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_spec__0(v_a_2840_, v_as_2839_, v___x_2844_, v___x_2845_);
return v___x_2846_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2839_ = stack[0].m_obj;
lean_object* v_a_2840_ = stack[1].m_obj;
uint8_t v_res_2847_;
v_res_2847_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_2839_, v_a_2840_);
stack->m_num = v_res_2847_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0___boxed(lean_object* v_as_2848_, lean_object* v_a_2849_){
_start:
{
uint8_t v_res_2850_; lean_object* v_r_2851_; 
v_res_2850_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_as_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_as_2848_);
v_r_2851_ = lean_box(v_res_2850_);
return v_r_2851_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11(void){
_start:
{
lean_object* v___x_2882_; lean_object* v_additional_2883_; lean_object* v___x_2884_; 
v___x_2882_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__10));
v_additional_2883_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2884_ = l_Array_append___redArg(v_additional_2883_, v___x_2882_);
return v___x_2884_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(lean_object* v_a_2885_){
_start:
{
lean_object* v_legalAxioms_2887_; lean_object* v_additional_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_legalAxioms_2887_ = lean_ctor_get(v_a_2885_, 5);
v_additional_2888_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_2889_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__3));
v___x_2890_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v_legalAxioms_2887_, v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; 
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_additional_2888_);
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11, &l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__11);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2885_ = stack[0].m_obj;
lean_object* v_res_2894_;
v_res_2894_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2885_);
stack->m_obj
 = v_res_2894_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___boxed(lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_2895_);
lean_dec_ref(v_a_2895_);
return v_res_2897_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(lean_object* v_e_2898_){
_start:
{
if (lean_obj_tag(v_e_2898_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2908_; 
v_a_2900_ = lean_ctor_get(v_e_2898_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_e_2898_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2902_ = v_e_2898_;
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v_e_2898_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_mk_io_user_error(v_a_2900_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set_tag(v___x_2902_, 1);
lean_ctor_set(v___x_2902_, 0, v___x_2904_);
v___x_2906_ = v___x_2902_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_a_2909_ = lean_ctor_get(v_e_2898_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_e_2898_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v_e_2898_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v_e_2898_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set_tag(v___x_2911_, 0);
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2898_ = stack[0].m_obj;
lean_object* v_res_2917_;
v_res_2917_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2898_);
stack->m_obj
 = v_res_2917_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg___boxed(lean_object* v_e_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2918_);
return v_res_2920_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_object* v_00_u03b1_2921_, lean_object* v_e_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v_e_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2922_ = stack[1].m_obj;
lean_object* v_res_2925_;
v_res_2925_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(lean_box(0), v_e_2922_);
stack->m_obj
 = v_res_2925_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_e_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0(v_00_u03b1_2926_, v_e_2927_);
return v_res_2929_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(lean_object* v_challengeExportPath_2930_, lean_object* v_solutionExportPath_2931_, lean_object* v_a_2932_){
_start:
{
uint8_t v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = 0;
v___x_2935_ = lean_io_prim_handle_mk(v_challengeExportPath_2930_, v___x_2934_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = lean_stream_of_handle(v_a_2936_);
v___x_2938_ = l_LeanExport_parseStream(v___x_2937_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = lean_io_prim_handle_mk(v_solutionExportPath_2931_, v___x_2934_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = lean_stream_of_handle(v_a_2941_);
v___x_2943_ = l_LeanExport_parseStream(v___x_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_theoremNames_2945_; lean_object* v_definitionNames_2946_; lean_object* v_legalAxioms_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc_n(v_a_2944_, 2);
lean_dec_ref_known(v___x_2943_, 1);
v_theoremNames_2945_ = lean_ctor_get(v_a_2932_, 3);
v_definitionNames_2946_ = lean_ctor_get(v_a_2932_, 4);
v_legalAxioms_2947_ = lean_ctor_get(v_a_2932_, 5);
lean_inc_ref(v_theoremNames_2945_);
v___x_2948_ = l_Array_append___redArg(v_theoremNames_2945_, v_legalAxioms_2947_);
v___x_2949_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
v___x_2951_ = l_Lake_Check_compareAt(v_a_2939_, v_a_2944_, v___x_2948_, v_definitionNames_2946_, v_a_2950_);
lean_dec_ref(v___x_2948_);
v___x_2952_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2951_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref_known(v___x_2952_, 1);
v___x_2953_ = l_Lake_Check_checkAxioms(v_a_2944_, v_theoremNames_2945_, v_definitionNames_2946_, v_legalAxioms_2947_);
v___x_2954_ = l_IO_ofExcept___at___00__private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_spec__0___redArg(v___x_2953_);
return v___x_2954_;
}
else
{
lean_dec(v_a_2944_);
return v___x_2952_;
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_a_2939_);
v_a_2955_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2943_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2943_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v_a_2939_);
v_a_2963_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2940_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2940_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2938_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2938_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v_a_2979_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2935_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2935_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare_0interp(lean_interpreter_value* stack)
{
lean_object* v_challengeExportPath_2930_ = stack[0].m_obj;
lean_object* v_solutionExportPath_2931_ = stack[1].m_obj;
lean_object* v_a_2932_ = stack[2].m_obj;
lean_object* v_res_2987_;
v_res_2987_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2930_, v_solutionExportPath_2931_, v_a_2932_);
stack->m_obj
 = v_res_2987_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare___boxed(lean_object* v_challengeExportPath_2988_, lean_object* v_solutionExportPath_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2988_, v_solutionExportPath_2989_, v_a_2990_);
lean_dec_ref(v_a_2990_);
lean_dec_ref(v_solutionExportPath_2989_);
lean_dec_ref(v_challengeExportPath_2988_);
return v_res_2992_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(lean_object* v_challengeExportPath_2993_, lean_object* v_solutionExportPath_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_verifyCompare(v_challengeExportPath_2993_, v_solutionExportPath_2994_, v_a_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v___x_2998_; 
lean_dec_ref_known(v___x_2997_, 1);
v___x_2998_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_solutionExportPath_2994_, v_a_2995_);
return v___x_2998_;
}
else
{
lean_dec_ref(v_solutionExportPath_2994_);
return v___x_2997_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_challengeExportPath_2993_ = stack[0].m_obj;
lean_object* v_solutionExportPath_2994_ = stack[1].m_obj;
lean_object* v_a_2995_ = stack[2].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_2993_, v_solutionExportPath_2994_, v_a_2995_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch___boxed(lean_object* v_challengeExportPath_3000_, lean_object* v_solutionExportPath_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_3000_, v_solutionExportPath_3001_, v_a_3002_);
lean_dec_ref(v_a_3002_);
lean_dec_ref(v_challengeExportPath_3000_);
return v_res_3004_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(lean_object* v_challengeExportPath_3006_, lean_object* v_solutionExportPath_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l___private_Lake_CLI_Check_0__Lake_Check_verifyMatch(v_challengeExportPath_3006_, v_solutionExportPath_3007_, v___y_3008_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref_known(v___x_3010_, 1);
v___x_3011_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___closed__0));
v___x_3012_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_3011_);
return v___x_3012_;
}
else
{
return v___x_3010_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_challengeExportPath_3006_ = stack[0].m_obj;
lean_object* v_solutionExportPath_3007_ = stack[1].m_obj;
lean_object* v___y_3008_ = stack[2].m_obj;
lean_object* v_res_3013_;
v_res_3013_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(v_challengeExportPath_3006_, v_solutionExportPath_3007_, v___y_3008_);
stack->m_obj
 = v_res_3013_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed(lean_object* v_challengeExportPath_3014_, lean_object* v_solutionExportPath_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0(v_challengeExportPath_3014_, v_solutionExportPath_3015_, v___y_3016_);
lean_dec_ref(v___y_3016_);
lean_dec_ref(v_challengeExportPath_3014_);
return v_res_3018_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(lean_object* v___x_3019_, lean_object* v_challengeExportPath_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_solutionModule_3023_; lean_object* v___f_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; 
v_solutionModule_3023_ = lean_ctor_get(v___y_3021_, 2);
v___f_3024_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3024_, 0, v_challengeExportPath_3020_);
v___x_3025_ = 1;
lean_inc(v_solutionModule_3023_);
v___x_3026_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_3025_, v_solutionModule_3023_, v___x_3019_, v___f_3024_, v___y_3021_);
return v___x_3026_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3019_ = stack[0].m_obj;
lean_object* v_challengeExportPath_3020_ = stack[1].m_obj;
lean_object* v___y_3021_ = stack[2].m_obj;
lean_object* v_res_3027_;
v_res_3027_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(v___x_3019_, v_challengeExportPath_3020_, v___y_3021_);
stack->m_obj
 = v_res_3027_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed(lean_object* v___x_3028_, lean_object* v_challengeExportPath_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1(v___x_3028_, v_challengeExportPath_3029_, v___y_3030_);
lean_dec_ref(v___y_3030_);
return v_res_3032_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt(lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3035_; lean_object* v_a_3036_; lean_object* v_challengeModule_3037_; lean_object* v_theoremNames_3038_; lean_object* v_definitionNames_3039_; lean_object* v_legalAxioms_3040_; lean_object* v___x_3041_; lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___f_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3035_ = l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets(v_a_3033_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref(v___x_3035_);
v_challengeModule_3037_ = lean_ctor_get(v_a_3033_, 1);
v_theoremNames_3038_ = lean_ctor_get(v_a_3033_, 3);
v_definitionNames_3039_ = lean_ctor_get(v_a_3033_, 4);
v_legalAxioms_3040_ = lean_ctor_get(v_a_3033_, 5);
v___x_3041_ = l___private_Lake_CLI_Check_0__Lake_Check_primitiveTargets___redArg();
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref(v___x_3041_);
v___x_3043_ = l_Array_append___redArg(v_a_3036_, v_theoremNames_3038_);
v___x_3044_ = l_Array_append___redArg(v___x_3043_, v_legalAxioms_3040_);
v___x_3045_ = l_Array_append___redArg(v___x_3044_, v_a_3042_);
lean_dec(v_a_3042_);
v___x_3046_ = l_Array_append___redArg(v___x_3045_, v_definitionNames_3039_);
lean_inc_ref(v___x_3046_);
v___f_3047_ = lean_alloc_closure((void*)(l___private_Lake_CLI_Check_0__Lake_Check_compareIt___lam__1___boxed), 4, 1);
lean_closure_set(v___f_3047_, 0, v___x_3046_);
v___x_3048_ = 2;
lean_inc(v_challengeModule_3037_);
v___x_3049_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeBuildAndExport___redArg(v___x_3048_, v_challengeModule_3037_, v___x_3046_, v___f_3047_, v_a_3033_);
return v___x_3049_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_compareIt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3033_ = stack[0].m_obj;
lean_object* v_res_3050_;
v_res_3050_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v_a_3033_);
stack->m_obj
 = v_res_3050_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_compareIt___boxed(lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v_a_3051_);
lean_dec_ref(v_a_3051_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(lean_object* v_j_3054_, lean_object* v_k_3055_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = l_Lean_Json_getObjValD(v_j_3054_, v_k_3055_);
v___x_3057_ = l_Lean_Json_getStr_x3f(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0___boxed(lean_object* v_j_3058_, lean_object* v_k_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_j_3058_, v_k_3059_);
lean_dec_ref(v_k_3059_);
return v_res_3060_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3061_, size_t v_i_3062_, lean_object* v_bs_3063_){
_start:
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_usize_dec_lt(v_i_3062_, v_sz_3061_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_bs_3063_);
return v___x_3065_;
}
else
{
lean_object* v_v_3066_; lean_object* v___x_3067_; 
v_v_3066_ = lean_array_uget_borrowed(v_bs_3063_, v_i_3062_);
lean_inc(v_v_3066_);
v___x_3067_ = l_Lean_Json_getStr_x3f(v_v_3066_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v_bs_3063_);
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3077_; lean_object* v_bs_x27_3078_; size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v_a_3076_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3077_ = lean_unsigned_to_nat(0u);
v_bs_x27_3078_ = lean_array_uset(v_bs_3063_, v_i_3062_, v___x_3077_);
v___x_3079_ = ((size_t)1ULL);
v___x_3080_ = lean_usize_add(v_i_3062_, v___x_3079_);
v___x_3081_ = lean_array_uset(v_bs_x27_3078_, v_i_3062_, v_a_3076_);
v_i_3062_ = v___x_3080_;
v_bs_3063_ = v___x_3081_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3061_ = stack[0].m_num;
size_t v_i_3062_ = stack[1].m_num;
lean_object* v_bs_3063_ = stack[2].m_obj;
lean_object* v_res_3083_;
v_res_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_3061_, v_i_3062_, v_bs_3063_);
stack->m_obj
 = v_res_3083_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3084_, lean_object* v_i_3085_, lean_object* v_bs_3086_){
_start:
{
size_t v_sz_boxed_3087_; size_t v_i_boxed_3088_; lean_object* v_res_3089_; 
v_sz_boxed_3087_ = lean_unbox_usize(v_sz_3084_);
lean_dec(v_sz_3084_);
v_i_boxed_3088_ = lean_unbox_usize(v_i_3085_);
lean_dec(v_i_3085_);
v_res_3089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3087_, v_i_boxed_3088_, v_bs_3086_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(lean_object* v_x_3092_){
_start:
{
if (lean_obj_tag(v_x_3092_) == 4)
{
lean_object* v_elems_3093_; size_t v_sz_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v_elems_3093_ = lean_ctor_get(v_x_3092_, 0);
lean_inc_ref(v_elems_3093_);
lean_dec_ref_known(v_x_3092_, 1);
v_sz_3094_ = lean_array_size(v_elems_3093_);
v___x_3095_ = ((size_t)0ULL);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1_spec__2(v_sz_3094_, v___x_3095_, v_elems_3093_);
return v___x_3096_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3097_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__0));
v___x_3098_ = lean_unsigned_to_nat(80u);
v___x_3099_ = l_Lean_Json_pretty(v_x_3092_, v___x_3098_);
v___x_3100_ = lean_string_append(v___x_3097_, v___x_3099_);
lean_dec_ref(v___x_3099_);
v___x_3101_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_3102_ = lean_string_append(v___x_3100_, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(lean_object* v_x_3106_){
_start:
{
if (lean_obj_tag(v_x_3106_) == 0)
{
lean_object* v___x_3107_; 
v___x_3107_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3___closed__0));
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_x_3106_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3125_; 
v_a_3117_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3119_ = v___x_3108_;
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3108_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_a_3117_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3121_);
v___x_3123_ = v___x_3119_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(lean_object* v_j_3126_, lean_object* v_k_3127_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = l_Lean_Json_getObjValD(v_j_3126_, v_k_3127_);
v___x_3129_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2_spec__3(v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2___boxed(lean_object* v_j_3130_, lean_object* v_k_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_j_3130_, v_k_3131_);
lean_dec_ref(v_k_3131_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(lean_object* v_x_3135_){
_start:
{
if (lean_obj_tag(v_x_3135_) == 0)
{
lean_object* v___x_3136_; 
v___x_3136_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___closed__0));
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Json_getBool_x3f(v_x_3135_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3154_; 
v_a_3146_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3148_ = v___x_3137_;
v_isShared_3149_ = v_isSharedCheck_3154_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3137_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3154_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v_a_3146_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v___x_3150_);
v___x_3152_ = v___x_3148_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5___boxed(lean_object* v_x_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v_x_3155_);
lean_dec(v_x_3155_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(lean_object* v_j_3157_, lean_object* v_k_3158_){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = l_Lean_Json_getObjValD(v_j_3157_, v_k_3158_);
v___x_3160_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3_spec__5(v___x_3159_);
lean_dec(v___x_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3___boxed(lean_object* v_j_3161_, lean_object* v_k_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_j_3161_, v_k_3162_);
lean_dec_ref(v_k_3162_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_cmp_3164_, lean_object* v_k_3165_, lean_object* v_v_3166_, lean_object* v_t_3167_){
_start:
{
if (lean_obj_tag(v_t_3167_) == 0)
{
lean_object* v_size_3168_; lean_object* v_k_3169_; lean_object* v_v_3170_; lean_object* v_l_3171_; lean_object* v_r_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3453_; 
v_size_3168_ = lean_ctor_get(v_t_3167_, 0);
v_k_3169_ = lean_ctor_get(v_t_3167_, 1);
v_v_3170_ = lean_ctor_get(v_t_3167_, 2);
v_l_3171_ = lean_ctor_get(v_t_3167_, 3);
v_r_3172_ = lean_ctor_get(v_t_3167_, 4);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_t_3167_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3174_ = v_t_3167_;
v_isShared_3175_ = v_isSharedCheck_3453_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_r_3172_);
lean_inc(v_l_3171_);
lean_inc(v_v_3170_);
lean_inc(v_k_3169_);
lean_inc(v_size_3168_);
lean_dec(v_t_3167_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3453_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; 
lean_inc_ref(v_cmp_3164_);
lean_inc(v_k_3169_);
lean_inc_ref(v_k_3165_);
v___x_3176_ = lean_apply_2(v_cmp_3164_, v_k_3165_, v_k_3169_);
v___x_3177_ = lean_unbox(v___x_3176_);
switch(v___x_3177_)
{
case 0:
{
lean_object* v_impl_3178_; lean_object* v___x_3179_; 
lean_dec(v_size_3168_);
v_impl_3178_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3164_, v_k_3165_, v_v_3166_, v_l_3171_);
v___x_3179_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3172_) == 0)
{
lean_object* v_size_3180_; lean_object* v_size_3181_; lean_object* v_k_3182_; lean_object* v_v_3183_; lean_object* v_l_3184_; lean_object* v_r_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; 
v_size_3180_ = lean_ctor_get(v_r_3172_, 0);
v_size_3181_ = lean_ctor_get(v_impl_3178_, 0);
v_k_3182_ = lean_ctor_get(v_impl_3178_, 1);
v_v_3183_ = lean_ctor_get(v_impl_3178_, 2);
v_l_3184_ = lean_ctor_get(v_impl_3178_, 3);
v_r_3185_ = lean_ctor_get(v_impl_3178_, 4);
lean_inc(v_r_3185_);
v___x_3186_ = lean_unsigned_to_nat(3u);
v___x_3187_ = lean_nat_mul(v___x_3186_, v_size_3180_);
v___x_3188_ = lean_nat_dec_lt(v___x_3187_, v_size_3181_);
lean_dec(v___x_3187_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3192_; 
lean_dec(v_r_3185_);
v___x_3189_ = lean_nat_add(v___x_3179_, v_size_3181_);
v___x_3190_ = lean_nat_add(v___x_3189_, v_size_3180_);
lean_dec(v___x_3189_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 3, v_impl_3178_);
lean_ctor_set(v___x_3174_, 0, v___x_3190_);
v___x_3192_ = v___x_3174_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_impl_3178_);
lean_ctor_set(v_reuseFailAlloc_3193_, 4, v_r_3172_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
else
{
lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3259_; 
lean_inc(v_l_3184_);
lean_inc(v_v_3183_);
lean_inc(v_k_3182_);
lean_inc(v_size_3181_);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_impl_3178_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; lean_object* v_unused_3261_; lean_object* v_unused_3262_; lean_object* v_unused_3263_; lean_object* v_unused_3264_; 
v_unused_3260_ = lean_ctor_get(v_impl_3178_, 4);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_impl_3178_, 3);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_impl_3178_, 2);
lean_dec(v_unused_3262_);
v_unused_3263_ = lean_ctor_get(v_impl_3178_, 1);
lean_dec(v_unused_3263_);
v_unused_3264_ = lean_ctor_get(v_impl_3178_, 0);
lean_dec(v_unused_3264_);
v___x_3195_ = v_impl_3178_;
v_isShared_3196_ = v_isSharedCheck_3259_;
goto v_resetjp_3194_;
}
else
{
lean_dec(v_impl_3178_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3259_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_size_3197_; lean_object* v_size_3198_; lean_object* v_k_3199_; lean_object* v_v_3200_; lean_object* v_l_3201_; lean_object* v_r_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v_size_3197_ = lean_ctor_get(v_l_3184_, 0);
v_size_3198_ = lean_ctor_get(v_r_3185_, 0);
v_k_3199_ = lean_ctor_get(v_r_3185_, 1);
v_v_3200_ = lean_ctor_get(v_r_3185_, 2);
v_l_3201_ = lean_ctor_get(v_r_3185_, 3);
v_r_3202_ = lean_ctor_get(v_r_3185_, 4);
v___x_3203_ = lean_unsigned_to_nat(2u);
v___x_3204_ = lean_nat_mul(v___x_3203_, v_size_3197_);
v___x_3205_ = lean_nat_dec_lt(v_size_3198_, v___x_3204_);
lean_dec(v___x_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3234_; 
lean_inc(v_r_3202_);
lean_inc(v_l_3201_);
lean_inc(v_v_3200_);
lean_inc(v_k_3199_);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_r_3185_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; lean_object* v_unused_3236_; lean_object* v_unused_3237_; lean_object* v_unused_3238_; lean_object* v_unused_3239_; 
v_unused_3235_ = lean_ctor_get(v_r_3185_, 4);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_r_3185_, 3);
lean_dec(v_unused_3236_);
v_unused_3237_ = lean_ctor_get(v_r_3185_, 2);
lean_dec(v_unused_3237_);
v_unused_3238_ = lean_ctor_get(v_r_3185_, 1);
lean_dec(v_unused_3238_);
v_unused_3239_ = lean_ctor_get(v_r_3185_, 0);
lean_dec(v_unused_3239_);
v___x_3207_ = v_r_3185_;
v_isShared_3208_ = v_isSharedCheck_3234_;
goto v_resetjp_3206_;
}
else
{
lean_dec(v_r_3185_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3234_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___x_3222_; lean_object* v___y_3224_; 
v___x_3209_ = lean_nat_add(v___x_3179_, v_size_3181_);
lean_dec(v_size_3181_);
v___x_3210_ = lean_nat_add(v___x_3209_, v_size_3180_);
lean_dec(v___x_3209_);
v___x_3222_ = lean_nat_add(v___x_3179_, v_size_3197_);
if (lean_obj_tag(v_l_3201_) == 0)
{
lean_object* v_size_3232_; 
v_size_3232_ = lean_ctor_get(v_l_3201_, 0);
lean_inc(v_size_3232_);
v___y_3224_ = v_size_3232_;
goto v___jp_3223_;
}
else
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_unsigned_to_nat(0u);
v___y_3224_ = v___x_3233_;
goto v___jp_3223_;
}
v___jp_3211_:
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3215_ = lean_nat_add(v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec(v___y_3213_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 4, v_r_3172_);
lean_ctor_set(v___x_3207_, 3, v_r_3202_);
lean_ctor_set(v___x_3207_, 2, v_v_3170_);
lean_ctor_set(v___x_3207_, 1, v_k_3169_);
lean_ctor_set(v___x_3207_, 0, v___x_3215_);
v___x_3217_ = v___x_3207_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v_r_3202_);
lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_r_3172_);
v___x_3217_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3219_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 4, v___x_3217_);
lean_ctor_set(v___x_3195_, 3, v___y_3212_);
lean_ctor_set(v___x_3195_, 2, v_v_3200_);
lean_ctor_set(v___x_3195_, 1, v_k_3199_);
lean_ctor_set(v___x_3195_, 0, v___x_3210_);
v___x_3219_ = v___x_3195_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_k_3199_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_v_3200_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v___y_3212_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
v___jp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3225_ = lean_nat_add(v___x_3222_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec(v___x_3222_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_l_3201_);
lean_ctor_set(v___x_3174_, 3, v_l_3184_);
lean_ctor_set(v___x_3174_, 2, v_v_3183_);
lean_ctor_set(v___x_3174_, 1, v_k_3182_);
lean_ctor_set(v___x_3174_, 0, v___x_3225_);
v___x_3227_ = v___x_3174_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_k_3182_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_v_3183_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_l_3184_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v_l_3201_);
v___x_3227_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_nat_add(v___x_3179_, v_size_3180_);
if (lean_obj_tag(v_r_3202_) == 0)
{
lean_object* v_size_3229_; 
v_size_3229_ = lean_ctor_get(v_r_3202_, 0);
lean_inc(v_size_3229_);
v___y_3212_ = v___x_3227_;
v___y_3213_ = v___x_3228_;
v___y_3214_ = v_size_3229_;
goto v___jp_3211_;
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_unsigned_to_nat(0u);
v___y_3212_ = v___x_3227_;
v___y_3213_ = v___x_3228_;
v___y_3214_ = v___x_3230_;
goto v___jp_3211_;
}
}
}
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
lean_del_object(v___x_3174_);
v___x_3240_ = lean_nat_add(v___x_3179_, v_size_3181_);
lean_dec(v_size_3181_);
v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3180_);
lean_dec(v___x_3240_);
v___x_3242_ = lean_nat_add(v___x_3179_, v_size_3180_);
v___x_3243_ = lean_nat_add(v___x_3242_, v_size_3198_);
lean_dec(v___x_3242_);
lean_inc_ref(v_r_3172_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 4, v_r_3172_);
lean_ctor_set(v___x_3195_, 3, v_r_3185_);
lean_ctor_set(v___x_3195_, 2, v_v_3170_);
lean_ctor_set(v___x_3195_, 1, v_k_3169_);
lean_ctor_set(v___x_3195_, 0, v___x_3243_);
v___x_3245_ = v___x_3195_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v_r_3185_);
lean_ctor_set(v_reuseFailAlloc_3258_, 4, v_r_3172_);
v___x_3245_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_isSharedCheck_3252_ = !lean_is_exclusive(v_r_3172_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; lean_object* v_unused_3254_; lean_object* v_unused_3255_; lean_object* v_unused_3256_; lean_object* v_unused_3257_; 
v_unused_3253_ = lean_ctor_get(v_r_3172_, 4);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v_r_3172_, 3);
lean_dec(v_unused_3254_);
v_unused_3255_ = lean_ctor_get(v_r_3172_, 2);
lean_dec(v_unused_3255_);
v_unused_3256_ = lean_ctor_get(v_r_3172_, 1);
lean_dec(v_unused_3256_);
v_unused_3257_ = lean_ctor_get(v_r_3172_, 0);
lean_dec(v_unused_3257_);
v___x_3247_ = v_r_3172_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_dec(v_r_3172_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v___x_3245_);
lean_ctor_set(v___x_3247_, 3, v_l_3184_);
lean_ctor_set(v___x_3247_, 2, v_v_3183_);
lean_ctor_set(v___x_3247_, 1, v_k_3182_);
lean_ctor_set(v___x_3247_, 0, v___x_3241_);
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v_k_3182_);
lean_ctor_set(v_reuseFailAlloc_3251_, 2, v_v_3183_);
lean_ctor_set(v_reuseFailAlloc_3251_, 3, v_l_3184_);
lean_ctor_set(v_reuseFailAlloc_3251_, 4, v___x_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3265_; 
v_l_3265_ = lean_ctor_get(v_impl_3178_, 3);
if (lean_obj_tag(v_l_3265_) == 0)
{
lean_object* v_r_3266_; lean_object* v_k_3267_; lean_object* v_v_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3279_; 
lean_inc_ref(v_l_3265_);
v_r_3266_ = lean_ctor_get(v_impl_3178_, 4);
v_k_3267_ = lean_ctor_get(v_impl_3178_, 1);
v_v_3268_ = lean_ctor_get(v_impl_3178_, 2);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_impl_3178_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; lean_object* v_unused_3281_; 
v_unused_3280_ = lean_ctor_get(v_impl_3178_, 3);
lean_dec(v_unused_3280_);
v_unused_3281_ = lean_ctor_get(v_impl_3178_, 0);
lean_dec(v_unused_3281_);
v___x_3270_ = v_impl_3178_;
v_isShared_3271_ = v_isSharedCheck_3279_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_r_3266_);
lean_inc(v_v_3268_);
lean_inc(v_k_3267_);
lean_dec(v_impl_3178_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3279_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3266_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 3, v_r_3266_);
lean_ctor_set(v___x_3270_, 2, v_v_3170_);
lean_ctor_set(v___x_3270_, 1, v_k_3169_);
lean_ctor_set(v___x_3270_, 0, v___x_3179_);
v___x_3274_ = v___x_3270_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3278_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3278_, 3, v_r_3266_);
lean_ctor_set(v_reuseFailAlloc_3278_, 4, v_r_3266_);
v___x_3274_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3276_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v___x_3274_);
lean_ctor_set(v___x_3174_, 3, v_l_3265_);
lean_ctor_set(v___x_3174_, 2, v_v_3268_);
lean_ctor_set(v___x_3174_, 1, v_k_3267_);
lean_ctor_set(v___x_3174_, 0, v___x_3272_);
v___x_3276_ = v___x_3174_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_k_3267_);
lean_ctor_set(v_reuseFailAlloc_3277_, 2, v_v_3268_);
lean_ctor_set(v_reuseFailAlloc_3277_, 3, v_l_3265_);
lean_ctor_set(v_reuseFailAlloc_3277_, 4, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_object* v_r_3282_; 
v_r_3282_ = lean_ctor_get(v_impl_3178_, 4);
lean_inc(v_r_3282_);
if (lean_obj_tag(v_r_3282_) == 0)
{
lean_object* v_k_3283_; lean_object* v_v_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3307_; 
lean_inc(v_l_3265_);
v_k_3283_ = lean_ctor_get(v_impl_3178_, 1);
v_v_3284_ = lean_ctor_get(v_impl_3178_, 2);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_impl_3178_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; 
v_unused_3308_ = lean_ctor_get(v_impl_3178_, 4);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_impl_3178_, 3);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_impl_3178_, 0);
lean_dec(v_unused_3310_);
v___x_3286_ = v_impl_3178_;
v_isShared_3287_ = v_isSharedCheck_3307_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_v_3284_);
lean_inc(v_k_3283_);
lean_dec(v_impl_3178_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3307_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_k_3288_; lean_object* v_v_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3303_; 
v_k_3288_ = lean_ctor_get(v_r_3282_, 1);
v_v_3289_ = lean_ctor_get(v_r_3282_, 2);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_r_3282_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; 
v_unused_3304_ = lean_ctor_get(v_r_3282_, 4);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_r_3282_, 3);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_r_3282_, 0);
lean_dec(v_unused_3306_);
v___x_3291_ = v_r_3282_;
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_v_3289_);
lean_inc(v_k_3288_);
lean_dec(v_r_3282_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_unsigned_to_nat(3u);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 4, v_l_3265_);
lean_ctor_set(v___x_3291_, 3, v_l_3265_);
lean_ctor_set(v___x_3291_, 2, v_v_3284_);
lean_ctor_set(v___x_3291_, 1, v_k_3283_);
lean_ctor_set(v___x_3291_, 0, v___x_3179_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_k_3283_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_v_3284_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_l_3265_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_l_3265_);
v___x_3295_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 4, v_l_3265_);
lean_ctor_set(v___x_3286_, 2, v_v_3170_);
lean_ctor_set(v___x_3286_, 1, v_k_3169_);
lean_ctor_set(v___x_3286_, 0, v___x_3179_);
v___x_3297_ = v___x_3286_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_l_3265_);
lean_ctor_set(v_reuseFailAlloc_3301_, 4, v_l_3265_);
v___x_3297_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v___x_3297_);
lean_ctor_set(v___x_3174_, 3, v___x_3295_);
lean_ctor_set(v___x_3174_, 2, v_v_3289_);
lean_ctor_set(v___x_3174_, 1, v_k_3288_);
lean_ctor_set(v___x_3174_, 0, v___x_3293_);
v___x_3299_ = v___x_3174_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v___x_3297_);
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
else
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_unsigned_to_nat(2u);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_r_3282_);
lean_ctor_set(v___x_3174_, 3, v_impl_3178_);
lean_ctor_set(v___x_3174_, 0, v___x_3311_);
v___x_3313_ = v___x_3174_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_impl_3178_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_r_3282_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3316_; 
lean_dec(v_v_3170_);
lean_dec(v_k_3169_);
lean_dec_ref(v_cmp_3164_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 2, v_v_3166_);
lean_ctor_set(v___x_3174_, 1, v_k_3165_);
v___x_3316_ = v___x_3174_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_size_3168_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_k_3165_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_v_3166_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_l_3171_);
lean_ctor_set(v_reuseFailAlloc_3317_, 4, v_r_3172_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
default: 
{
lean_object* v_impl_3318_; lean_object* v___x_3319_; 
lean_dec(v_size_3168_);
v_impl_3318_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3164_, v_k_3165_, v_v_3166_, v_r_3172_);
v___x_3319_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3171_) == 0)
{
lean_object* v_size_3320_; lean_object* v_size_3321_; lean_object* v_k_3322_; lean_object* v_v_3323_; lean_object* v_l_3324_; lean_object* v_r_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v_size_3320_ = lean_ctor_get(v_l_3171_, 0);
v_size_3321_ = lean_ctor_get(v_impl_3318_, 0);
v_k_3322_ = lean_ctor_get(v_impl_3318_, 1);
v_v_3323_ = lean_ctor_get(v_impl_3318_, 2);
v_l_3324_ = lean_ctor_get(v_impl_3318_, 3);
lean_inc(v_l_3324_);
v_r_3325_ = lean_ctor_get(v_impl_3318_, 4);
v___x_3326_ = lean_unsigned_to_nat(3u);
v___x_3327_ = lean_nat_mul(v___x_3326_, v_size_3320_);
v___x_3328_ = lean_nat_dec_lt(v___x_3327_, v_size_3321_);
lean_dec(v___x_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
lean_dec(v_l_3324_);
v___x_3329_ = lean_nat_add(v___x_3319_, v_size_3320_);
v___x_3330_ = lean_nat_add(v___x_3329_, v_size_3321_);
lean_dec(v___x_3329_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_impl_3318_);
lean_ctor_set(v___x_3174_, 0, v___x_3330_);
v___x_3332_ = v___x_3174_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v_l_3171_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v_impl_3318_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
else
{
lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3397_; 
lean_inc(v_r_3325_);
lean_inc(v_v_3323_);
lean_inc(v_k_3322_);
lean_inc(v_size_3321_);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_impl_3318_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; lean_object* v_unused_3399_; lean_object* v_unused_3400_; lean_object* v_unused_3401_; lean_object* v_unused_3402_; 
v_unused_3398_ = lean_ctor_get(v_impl_3318_, 4);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_impl_3318_, 3);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_impl_3318_, 2);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_impl_3318_, 1);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_impl_3318_, 0);
lean_dec(v_unused_3402_);
v___x_3335_ = v_impl_3318_;
v_isShared_3336_ = v_isSharedCheck_3397_;
goto v_resetjp_3334_;
}
else
{
lean_dec(v_impl_3318_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3397_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v_size_3337_; lean_object* v_k_3338_; lean_object* v_v_3339_; lean_object* v_l_3340_; lean_object* v_r_3341_; lean_object* v_size_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_size_3337_ = lean_ctor_get(v_l_3324_, 0);
v_k_3338_ = lean_ctor_get(v_l_3324_, 1);
v_v_3339_ = lean_ctor_get(v_l_3324_, 2);
v_l_3340_ = lean_ctor_get(v_l_3324_, 3);
v_r_3341_ = lean_ctor_get(v_l_3324_, 4);
v_size_3342_ = lean_ctor_get(v_r_3325_, 0);
v___x_3343_ = lean_unsigned_to_nat(2u);
v___x_3344_ = lean_nat_mul(v___x_3343_, v_size_3342_);
v___x_3345_ = lean_nat_dec_lt(v_size_3337_, v___x_3344_);
lean_dec(v___x_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3373_; 
lean_inc(v_r_3341_);
lean_inc(v_l_3340_);
lean_inc(v_v_3339_);
lean_inc(v_k_3338_);
v_isSharedCheck_3373_ = !lean_is_exclusive(v_l_3324_);
if (v_isSharedCheck_3373_ == 0)
{
lean_object* v_unused_3374_; lean_object* v_unused_3375_; lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; 
v_unused_3374_ = lean_ctor_get(v_l_3324_, 4);
lean_dec(v_unused_3374_);
v_unused_3375_ = lean_ctor_get(v_l_3324_, 3);
lean_dec(v_unused_3375_);
v_unused_3376_ = lean_ctor_get(v_l_3324_, 2);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_l_3324_, 1);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_l_3324_, 0);
lean_dec(v_unused_3378_);
v___x_3347_ = v_l_3324_;
v_isShared_3348_ = v_isSharedCheck_3373_;
goto v_resetjp_3346_;
}
else
{
lean_dec(v_l_3324_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3373_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3363_; 
v___x_3349_ = lean_nat_add(v___x_3319_, v_size_3320_);
v___x_3350_ = lean_nat_add(v___x_3349_, v_size_3321_);
lean_dec(v_size_3321_);
if (lean_obj_tag(v_l_3340_) == 0)
{
lean_object* v_size_3371_; 
v_size_3371_ = lean_ctor_get(v_l_3340_, 0);
lean_inc(v_size_3371_);
v___y_3363_ = v_size_3371_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_unsigned_to_nat(0u);
v___y_3363_ = v___x_3372_;
goto v___jp_3362_;
}
v___jp_3351_:
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3355_ = lean_nat_add(v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 4, v_r_3325_);
lean_ctor_set(v___x_3347_, 3, v_r_3341_);
lean_ctor_set(v___x_3347_, 2, v_v_3323_);
lean_ctor_set(v___x_3347_, 1, v_k_3322_);
lean_ctor_set(v___x_3347_, 0, v___x_3355_);
v___x_3357_ = v___x_3347_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_k_3322_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_v_3323_);
lean_ctor_set(v_reuseFailAlloc_3361_, 3, v_r_3341_);
lean_ctor_set(v_reuseFailAlloc_3361_, 4, v_r_3325_);
v___x_3357_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3359_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v___x_3357_);
lean_ctor_set(v___x_3335_, 3, v___y_3352_);
lean_ctor_set(v___x_3335_, 2, v_v_3339_);
lean_ctor_set(v___x_3335_, 1, v_k_3338_);
lean_ctor_set(v___x_3335_, 0, v___x_3350_);
v___x_3359_ = v___x_3335_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3360_, 3, v___y_3352_);
lean_ctor_set(v_reuseFailAlloc_3360_, 4, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
v___jp_3362_:
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3364_ = lean_nat_add(v___x_3349_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec(v___x_3349_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_l_3340_);
lean_ctor_set(v___x_3174_, 0, v___x_3364_);
v___x_3366_ = v___x_3174_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_l_3171_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_l_3340_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_nat_add(v___x_3319_, v_size_3342_);
if (lean_obj_tag(v_r_3341_) == 0)
{
lean_object* v_size_3368_; 
v_size_3368_ = lean_ctor_get(v_r_3341_, 0);
lean_inc(v_size_3368_);
v___y_3352_ = v___x_3366_;
v___y_3353_ = v___x_3367_;
v___y_3354_ = v_size_3368_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_unsigned_to_nat(0u);
v___y_3352_ = v___x_3366_;
v___y_3353_ = v___x_3367_;
v___y_3354_ = v___x_3369_;
goto v___jp_3351_;
}
}
}
}
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_del_object(v___x_3174_);
v___x_3379_ = lean_nat_add(v___x_3319_, v_size_3320_);
v___x_3380_ = lean_nat_add(v___x_3379_, v_size_3321_);
lean_dec(v_size_3321_);
v___x_3381_ = lean_nat_add(v___x_3379_, v_size_3337_);
lean_dec(v___x_3379_);
lean_inc_ref(v_l_3171_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 4, v_l_3324_);
lean_ctor_set(v___x_3335_, 3, v_l_3171_);
lean_ctor_set(v___x_3335_, 2, v_v_3170_);
lean_ctor_set(v___x_3335_, 1, v_k_3169_);
lean_ctor_set(v___x_3335_, 0, v___x_3381_);
v___x_3383_ = v___x_3335_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3396_, 3, v_l_3171_);
lean_ctor_set(v_reuseFailAlloc_3396_, 4, v_l_3324_);
v___x_3383_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
v_isSharedCheck_3390_ = !lean_is_exclusive(v_l_3171_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; lean_object* v_unused_3392_; lean_object* v_unused_3393_; lean_object* v_unused_3394_; lean_object* v_unused_3395_; 
v_unused_3391_ = lean_ctor_get(v_l_3171_, 4);
lean_dec(v_unused_3391_);
v_unused_3392_ = lean_ctor_get(v_l_3171_, 3);
lean_dec(v_unused_3392_);
v_unused_3393_ = lean_ctor_get(v_l_3171_, 2);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_l_3171_, 1);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_l_3171_, 0);
lean_dec(v_unused_3395_);
v___x_3385_ = v_l_3171_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_dec(v_l_3171_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 4, v_r_3325_);
lean_ctor_set(v___x_3385_, 3, v___x_3383_);
lean_ctor_set(v___x_3385_, 2, v_v_3323_);
lean_ctor_set(v___x_3385_, 1, v_k_3322_);
lean_ctor_set(v___x_3385_, 0, v___x_3380_);
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_k_3322_);
lean_ctor_set(v_reuseFailAlloc_3389_, 2, v_v_3323_);
lean_ctor_set(v_reuseFailAlloc_3389_, 3, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3389_, 4, v_r_3325_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3403_; 
v_l_3403_ = lean_ctor_get(v_impl_3318_, 3);
lean_inc(v_l_3403_);
if (lean_obj_tag(v_l_3403_) == 0)
{
lean_object* v_r_3404_; lean_object* v_k_3405_; lean_object* v_v_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3429_; 
v_r_3404_ = lean_ctor_get(v_impl_3318_, 4);
v_k_3405_ = lean_ctor_get(v_impl_3318_, 1);
v_v_3406_ = lean_ctor_get(v_impl_3318_, 2);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_impl_3318_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; lean_object* v_unused_3431_; 
v_unused_3430_ = lean_ctor_get(v_impl_3318_, 3);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v_impl_3318_, 0);
lean_dec(v_unused_3431_);
v___x_3408_ = v_impl_3318_;
v_isShared_3409_ = v_isSharedCheck_3429_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_r_3404_);
lean_inc(v_v_3406_);
lean_inc(v_k_3405_);
lean_dec(v_impl_3318_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3429_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_k_3410_; lean_object* v_v_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3425_; 
v_k_3410_ = lean_ctor_get(v_l_3403_, 1);
v_v_3411_ = lean_ctor_get(v_l_3403_, 2);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_l_3403_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; lean_object* v_unused_3428_; 
v_unused_3426_ = lean_ctor_get(v_l_3403_, 4);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_l_3403_, 3);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_l_3403_, 0);
lean_dec(v_unused_3428_);
v___x_3413_ = v_l_3403_;
v_isShared_3414_ = v_isSharedCheck_3425_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_v_3411_);
lean_inc(v_k_3410_);
lean_dec(v_l_3403_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3425_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3404_, 2);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 4, v_r_3404_);
lean_ctor_set(v___x_3413_, 3, v_r_3404_);
lean_ctor_set(v___x_3413_, 2, v_v_3170_);
lean_ctor_set(v___x_3413_, 1, v_k_3169_);
lean_ctor_set(v___x_3413_, 0, v___x_3319_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_r_3404_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_r_3404_);
v___x_3417_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
lean_inc(v_r_3404_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 3, v_r_3404_);
lean_ctor_set(v___x_3408_, 0, v___x_3319_);
v___x_3419_ = v___x_3408_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_k_3405_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_v_3406_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v_r_3404_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_r_3404_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v___x_3419_);
lean_ctor_set(v___x_3174_, 3, v___x_3417_);
lean_ctor_set(v___x_3174_, 2, v_v_3411_);
lean_ctor_set(v___x_3174_, 1, v_k_3410_);
lean_ctor_set(v___x_3174_, 0, v___x_3415_);
v___x_3421_ = v___x_3174_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_k_3410_);
lean_ctor_set(v_reuseFailAlloc_3422_, 2, v_v_3411_);
lean_ctor_set(v_reuseFailAlloc_3422_, 3, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3422_, 4, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
}
else
{
lean_object* v_r_3432_; 
v_r_3432_ = lean_ctor_get(v_impl_3318_, 4);
lean_inc(v_r_3432_);
if (lean_obj_tag(v_r_3432_) == 0)
{
lean_object* v_k_3433_; lean_object* v_v_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3445_; 
v_k_3433_ = lean_ctor_get(v_impl_3318_, 1);
v_v_3434_ = lean_ctor_get(v_impl_3318_, 2);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_impl_3318_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; lean_object* v_unused_3447_; lean_object* v_unused_3448_; 
v_unused_3446_ = lean_ctor_get(v_impl_3318_, 4);
lean_dec(v_unused_3446_);
v_unused_3447_ = lean_ctor_get(v_impl_3318_, 3);
lean_dec(v_unused_3447_);
v_unused_3448_ = lean_ctor_get(v_impl_3318_, 0);
lean_dec(v_unused_3448_);
v___x_3436_ = v_impl_3318_;
v_isShared_3437_ = v_isSharedCheck_3445_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_v_3434_);
lean_inc(v_k_3433_);
lean_dec(v_impl_3318_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3445_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3438_ = lean_unsigned_to_nat(3u);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_l_3403_);
lean_ctor_set(v___x_3436_, 2, v_v_3170_);
lean_ctor_set(v___x_3436_, 1, v_k_3169_);
lean_ctor_set(v___x_3436_, 0, v___x_3319_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3319_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_l_3403_);
lean_ctor_set(v_reuseFailAlloc_3444_, 4, v_l_3403_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_r_3432_);
lean_ctor_set(v___x_3174_, 3, v___x_3440_);
lean_ctor_set(v___x_3174_, 2, v_v_3434_);
lean_ctor_set(v___x_3174_, 1, v_k_3433_);
lean_ctor_set(v___x_3174_, 0, v___x_3438_);
v___x_3442_ = v___x_3174_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_k_3433_);
lean_ctor_set(v_reuseFailAlloc_3443_, 2, v_v_3434_);
lean_ctor_set(v_reuseFailAlloc_3443_, 3, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3443_, 4, v_r_3432_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_unsigned_to_nat(2u);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 4, v_impl_3318_);
lean_ctor_set(v___x_3174_, 3, v_r_3432_);
lean_ctor_set(v___x_3174_, 0, v___x_3449_);
v___x_3451_ = v___x_3174_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_r_3432_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_impl_3318_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
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
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_dec_ref(v_cmp_3164_);
v___x_3454_ = lean_unsigned_to_nat(1u);
v___x_3455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
lean_ctor_set(v___x_3455_, 1, v_k_3165_);
lean_ctor_set(v___x_3455_, 2, v_v_3166_);
lean_ctor_set(v___x_3455_, 3, v_t_3167_);
lean_ctor_set(v___x_3455_, 4, v_t_3167_);
return v___x_3455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(lean_object* v_cmp_3456_, lean_object* v_init_3457_, lean_object* v_x_3458_){
_start:
{
if (lean_obj_tag(v_x_3458_) == 0)
{
lean_object* v_k_3459_; lean_object* v_v_3460_; lean_object* v_l_3461_; lean_object* v_r_3462_; lean_object* v___x_3463_; 
v_k_3459_ = lean_ctor_get(v_x_3458_, 1);
lean_inc(v_k_3459_);
v_v_3460_ = lean_ctor_get(v_x_3458_, 2);
lean_inc(v_v_3460_);
v_l_3461_ = lean_ctor_get(v_x_3458_, 3);
lean_inc(v_l_3461_);
v_r_3462_ = lean_ctor_get(v_x_3458_, 4);
lean_inc(v_r_3462_);
lean_dec_ref_known(v_x_3458_, 5);
lean_inc_ref(v_cmp_3456_);
v___x_3463_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3456_, v_init_3457_, v_l_3461_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_dec(v_r_3462_);
lean_dec(v_v_3460_);
lean_dec(v_k_3459_);
lean_dec_ref(v_cmp_3456_);
return v___x_3463_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3465_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref_known(v___x_3463_, 1);
v___x_3465_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v_v_3460_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_a_3464_);
lean_dec(v_r_3462_);
lean_dec(v_k_3459_);
lean_dec_ref(v_cmp_3456_);
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3465_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3465_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3475_; 
v_a_3474_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3465_, 1);
lean_inc_ref(v_cmp_3456_);
v___x_3475_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3456_, v_k_3459_, v_a_3474_, v_a_3464_);
v_init_3457_ = v___x_3475_;
v_x_3458_ = v_r_3462_;
goto _start;
}
}
}
else
{
lean_object* v___x_3477_; 
lean_dec_ref(v_cmp_3456_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_init_3457_);
return v___x_3477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(lean_object* v_cmp_3478_, lean_object* v_j_3479_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Json_getObj_x3f(v_j_3479_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec_ref(v_cmp_3478_);
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_a_3489_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3489_);
lean_dec_ref_known(v___x_3480_, 1);
v___x_3490_ = lean_box(1);
v___x_3491_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__11(v_cmp_3478_, v___x_3490_, v_a_3489_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(lean_object* v_x_3495_){
_start:
{
if (lean_obj_tag(v_x_3495_) == 0)
{
lean_object* v___x_3496_; 
v___x_3496_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__0));
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7___closed__1));
v___x_3498_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9(v___x_3497_, v_x_3495_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3515_; 
v_a_3507_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3509_ = v___x_3498_;
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3498_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3511_, 0, v_a_3507_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3511_);
v___x_3513_ = v___x_3509_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(lean_object* v_j_3516_, lean_object* v_k_3517_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = l_Lean_Json_getObjValD(v_j_3516_, v_k_3517_);
v___x_3519_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7(v___x_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4___boxed(lean_object* v_j_3520_, lean_object* v_k_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_j_3520_, v_k_3521_);
lean_dec_ref(v_k_3521_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(lean_object* v_j_3523_, lean_object* v_k_3524_){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = l_Lean_Json_getObjValD(v_j_3523_, v_k_3524_);
v___x_3526_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1(v___x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1___boxed(lean_object* v_j_3527_, lean_object* v_k_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_j_3527_, v_k_3528_);
lean_dec_ref(v_k_3528_);
return v_res_3529_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = 1;
v___x_3539_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__4));
v___x_3540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3539_, v___x_3538_);
return v___x_3540_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__6));
v___x_3543_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__5, &l_Lake_Check_instFromJsonConfig_fromJson___closed__5_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__5);
v___x_3544_ = lean_string_append(v___x_3543_, v___x_3542_);
return v___x_3544_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3547_ = 1;
v___x_3548_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__8));
v___x_3549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3548_, v___x_3547_);
return v___x_3549_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__9, &l_Lake_Check_instFromJsonConfig_fromJson___closed__9_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__9);
v___x_3551_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3552_ = lean_string_append(v___x_3551_, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3555_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__10, &l_Lake_Check_instFromJsonConfig_fromJson___closed__10_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__10);
v___x_3556_ = lean_string_append(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = 1;
v___x_3561_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__14));
v___x_3562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__15, &l_Lake_Check_instFromJsonConfig_fromJson___closed__15_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__15);
v___x_3564_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3565_ = lean_string_append(v___x_3564_, v___x_3563_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3567_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__16, &l_Lake_Check_instFromJsonConfig_fromJson___closed__16_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__16);
v___x_3568_ = lean_string_append(v___x_3567_, v___x_3566_);
return v___x_3568_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20(void){
_start:
{
uint8_t v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3572_ = 1;
v___x_3573_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__19));
v___x_3574_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3573_, v___x_3572_);
return v___x_3574_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3575_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__20, &l_Lake_Check_instFromJsonConfig_fromJson___closed__20_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__20);
v___x_3576_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3577_ = lean_string_append(v___x_3576_, v___x_3575_);
return v___x_3577_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3579_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__21, &l_Lake_Check_instFromJsonConfig_fromJson___closed__21_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__21);
v___x_3580_ = lean_string_append(v___x_3579_, v___x_3578_);
return v___x_3580_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25(void){
_start:
{
uint8_t v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3584_ = 1;
v___x_3585_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__24));
v___x_3586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3585_, v___x_3584_);
return v___x_3586_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26(void){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3587_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__25, &l_Lake_Check_instFromJsonConfig_fromJson___closed__25_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__25);
v___x_3588_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3589_ = lean_string_append(v___x_3588_, v___x_3587_);
return v___x_3589_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3591_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__26, &l_Lake_Check_instFromJsonConfig_fromJson___closed__26_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__26);
v___x_3592_ = lean_string_append(v___x_3591_, v___x_3590_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29(void){
_start:
{
uint8_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = 1;
v___x_3596_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__28));
v___x_3597_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3596_, v___x_3595_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__29, &l_Lake_Check_instFromJsonConfig_fromJson___closed__29_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__29);
v___x_3599_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3600_ = lean_string_append(v___x_3599_, v___x_3598_);
return v___x_3600_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3601_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3602_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__30, &l_Lake_Check_instFromJsonConfig_fromJson___closed__30_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__30);
v___x_3603_ = lean_string_append(v___x_3602_, v___x_3601_);
return v___x_3603_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35(void){
_start:
{
uint8_t v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3608_ = 1;
v___x_3609_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__34));
v___x_3610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3609_, v___x_3608_);
return v___x_3610_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36(void){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__35, &l_Lake_Check_instFromJsonConfig_fromJson___closed__35_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__35);
v___x_3612_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3613_ = lean_string_append(v___x_3612_, v___x_3611_);
return v___x_3613_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37(void){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3615_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__36, &l_Lake_Check_instFromJsonConfig_fromJson___closed__36_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__36);
v___x_3616_ = lean_string_append(v___x_3615_, v___x_3614_);
return v___x_3616_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41(void){
_start:
{
uint8_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = 1;
v___x_3622_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__40));
v___x_3623_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3622_, v___x_3621_);
return v___x_3623_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__41, &l_Lake_Check_instFromJsonConfig_fromJson___closed__41_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__41);
v___x_3625_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__7, &l_Lake_Check_instFromJsonConfig_fromJson___closed__7_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__7);
v___x_3626_ = lean_string_append(v___x_3625_, v___x_3624_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43(void){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3627_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__11));
v___x_3628_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__42, &l_Lake_Check_instFromJsonConfig_fromJson___closed__42_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__42);
v___x_3629_ = lean_string_append(v___x_3628_, v___x_3627_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instFromJsonConfig_fromJson(lean_object* v_json_3630_){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
lean_inc(v_json_3630_);
v___x_3632_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3630_, v___x_3631_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3642_; 
lean_dec(v_json_3630_);
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3642_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3642_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
v___x_3637_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__12, &l_Lake_Check_instFromJsonConfig_fromJson___closed__12_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__12);
v___x_3638_ = lean_string_append(v___x_3637_, v_a_3633_);
lean_dec(v_a_3633_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3638_);
v___x_3640_ = v___x_3635_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
else
{
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec(v_json_3630_);
v_a_3643_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3632_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3632_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 0);
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v_a_3651_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3632_, 1);
v___x_3652_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
lean_inc(v_json_3630_);
v___x_3653_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__0(v_json_3630_, v___x_3652_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3663_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3663_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3658_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__17, &l_Lake_Check_instFromJsonConfig_fromJson___closed__17_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__17);
v___x_3659_ = lean_string_append(v___x_3658_, v_a_3654_);
lean_dec(v_a_3654_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3659_);
v___x_3661_ = v___x_3656_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3664_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3653_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3653_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set_tag(v___x_3666_, 0);
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v_a_3672_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3673_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
lean_inc(v_json_3630_);
v___x_3674_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3630_, v___x_3673_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3684_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3684_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3679_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__22, &l_Lake_Check_instFromJsonConfig_fromJson___closed__22_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__22);
v___x_3680_ = lean_string_append(v___x_3679_, v_a_3675_);
lean_dec(v_a_3675_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v___x_3680_);
v___x_3682_ = v___x_3677_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
else
{
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3685_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3674_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3674_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 0);
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_a_3693_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3674_, 1);
v___x_3694_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
lean_inc(v_json_3630_);
v___x_3695_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__2(v_json_3630_, v___x_3694_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3705_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3705_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3700_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__27, &l_Lake_Check_instFromJsonConfig_fromJson___closed__27_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__27);
v___x_3701_ = lean_string_append(v___x_3700_, v_a_3696_);
lean_dec(v_a_3696_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3701_);
v___x_3703_ = v___x_3698_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
else
{
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3706_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3695_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3695_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set_tag(v___x_3708_, 0);
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_a_3714_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3715_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
lean_inc(v_json_3630_);
v___x_3716_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1(v_json_3630_, v___x_3715_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_a_3714_);
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3719_ = v___x_3716_;
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3721_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__31, &l_Lake_Check_instFromJsonConfig_fromJson___closed__31_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__31);
v___x_3722_ = lean_string_append(v___x_3721_, v_a_3717_);
lean_dec(v_a_3717_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v___x_3722_);
v___x_3724_ = v___x_3719_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
else
{
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v_a_3714_);
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3727_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3716_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3716_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 0);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_a_3735_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3716_, 1);
v___x_3736_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
lean_inc(v_json_3630_);
v___x_3737_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__3(v_json_3630_, v___x_3736_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3747_; 
lean_dec(v_a_3735_);
lean_dec(v_a_3714_);
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3740_ = v___x_3737_;
v_isShared_3741_ = v_isSharedCheck_3747_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3737_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3747_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3745_; 
v___x_3742_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__37, &l_Lake_Check_instFromJsonConfig_fromJson___closed__37_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__37);
v___x_3743_ = lean_string_append(v___x_3742_, v_a_3738_);
lean_dec(v_a_3738_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3743_);
v___x_3745_ = v___x_3740_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
else
{
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v_a_3735_);
lean_dec(v_a_3714_);
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
lean_dec(v_json_3630_);
v_a_3748_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3737_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3737_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set_tag(v___x_3750_, 0);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_a_3756_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3737_, 1);
v___x_3757_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3758_ = l_Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4(v_json_3630_, v___x_3757_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3756_);
lean_dec(v_a_3735_);
lean_dec(v_a_3714_);
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3768_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3768_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3763_ = lean_obj_once(&l_Lake_Check_instFromJsonConfig_fromJson___closed__43, &l_Lake_Check_instFromJsonConfig_fromJson___closed__43_once, _init_l_Lake_Check_instFromJsonConfig_fromJson___closed__43);
v___x_3764_ = lean_string_append(v___x_3763_, v_a_3759_);
lean_dec(v_a_3759_);
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 0, v___x_3764_);
v___x_3766_ = v___x_3761_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec(v_a_3756_);
lean_dec(v_a_3735_);
lean_dec(v_a_3714_);
lean_dec(v_a_3693_);
lean_dec(v_a_3672_);
lean_dec(v_a_3651_);
v_a_3769_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3758_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3758_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
lean_ctor_set_tag(v___x_3771_, 0);
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3785_; 
v_a_3777_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3779_ = v___x_3758_;
v_isShared_3780_ = v_isSharedCheck_3785_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3758_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3785_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3781_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3781_, 0, v_a_3651_);
lean_ctor_set(v___x_3781_, 1, v_a_3672_);
lean_ctor_set(v___x_3781_, 2, v_a_3693_);
lean_ctor_set(v___x_3781_, 3, v_a_3714_);
lean_ctor_set(v___x_3781_, 4, v_a_3735_);
lean_ctor_set(v___x_3781_, 5, v_a_3756_);
lean_ctor_set(v___x_3781_, 6, v_a_3777_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3781_);
v___x_3783_ = v___x_3779_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10(lean_object* v_cmp_3786_, lean_object* v_00_u03b2_3787_, lean_object* v_k_3788_, lean_object* v_v_3789_, lean_object* v_t_3790_, lean_object* v_hl_3791_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__4_spec__7_spec__9_spec__10___redArg(v_cmp_3786_, v_k_3788_, v_v_3789_, v_t_3790_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(lean_object* v_k_3795_, lean_object* v_x_3796_){
_start:
{
if (lean_obj_tag(v_x_3796_) == 0)
{
lean_object* v___x_3797_; 
lean_dec_ref(v_k_3795_);
v___x_3797_ = lean_box(0);
return v___x_3797_;
}
else
{
lean_object* v_val_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_val_3798_ = lean_ctor_get(v_x_3796_, 0);
v___x_3799_ = lean_alloc_ctor(1, 0, 1);
v___x_3800_ = lean_unbox(v_val_3798_);
lean_ctor_set_uint8(v___x_3799_, 0, v___x_3800_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v_k_3795_);
lean_ctor_set(v___x_3801_, 1, v___x_3799_);
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
return v___x_3803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2___boxed(lean_object* v_k_3804_, lean_object* v_x_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v_k_3804_, v_x_3805_);
lean_dec(v_x_3805_);
return v_res_3806_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(size_t v_sz_3807_, size_t v_i_3808_, lean_object* v_bs_3809_){
_start:
{
uint8_t v___x_3810_; 
v___x_3810_ = lean_usize_dec_lt(v_i_3808_, v_sz_3807_);
if (v___x_3810_ == 0)
{
return v_bs_3809_;
}
else
{
lean_object* v_v_3811_; lean_object* v___x_3812_; lean_object* v_bs_x27_3813_; lean_object* v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; 
v_v_3811_ = lean_array_uget(v_bs_3809_, v_i_3808_);
v___x_3812_ = lean_unsigned_to_nat(0u);
v_bs_x27_3813_ = lean_array_uset(v_bs_3809_, v_i_3808_, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3814_, 0, v_v_3811_);
v___x_3815_ = ((size_t)1ULL);
v___x_3816_ = lean_usize_add(v_i_3808_, v___x_3815_);
v___x_3817_ = lean_array_uset(v_bs_x27_3813_, v_i_3808_, v___x_3814_);
v_i_3808_ = v___x_3816_;
v_bs_3809_ = v___x_3817_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3807_ = stack[0].m_num;
size_t v_i_3808_ = stack[1].m_num;
lean_object* v_bs_3809_ = stack[2].m_obj;
lean_object* v_res_3819_;
v_res_3819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_3807_, v_i_3808_, v_bs_3809_);
stack->m_obj
 = v_res_3819_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3820_, lean_object* v_i_3821_, lean_object* v_bs_3822_){
_start:
{
size_t v_sz_boxed_3823_; size_t v_i_boxed_3824_; lean_object* v_res_3825_; 
v_sz_boxed_3823_ = lean_unbox_usize(v_sz_3820_);
lean_dec(v_sz_3820_);
v_i_boxed_3824_ = lean_unbox_usize(v_i_3821_);
lean_dec(v_i_3821_);
v_res_3825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_boxed_3823_, v_i_boxed_3824_, v_bs_3822_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(lean_object* v_a_3826_){
_start:
{
size_t v_sz_3827_; size_t v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_sz_3827_ = lean_array_size(v_a_3826_);
v___x_3828_ = ((size_t)0ULL);
v___x_3829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0_spec__0(v_sz_3827_, v___x_3828_, v_a_3826_);
v___x_3830_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(lean_object* v_x_3831_){
_start:
{
if (lean_obj_tag(v_x_3831_) == 0)
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_box(0);
return v___x_3832_;
}
else
{
lean_object* v_val_3833_; lean_object* v___x_3834_; 
v_val_3833_ = lean_ctor_get(v_x_3831_, 0);
lean_inc(v_val_3833_);
lean_dec_ref_known(v_x_3831_, 1);
v___x_3834_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_val_3833_);
return v___x_3834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
if (lean_obj_tag(v_a_3835_) == 0)
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_array_to_list(v_a_3836_);
return v___x_3837_;
}
else
{
lean_object* v_head_3838_; lean_object* v_tail_3839_; lean_object* v___x_3840_; 
v_head_3838_ = lean_ctor_get(v_a_3835_, 0);
lean_inc(v_head_3838_);
v_tail_3839_ = lean_ctor_get(v_a_3835_, 1);
lean_inc(v_tail_3839_);
lean_dec_ref_known(v_a_3835_, 2);
v___x_3840_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3836_, v_head_3838_);
v_a_3835_ = v_tail_3839_;
v_a_3836_ = v___x_3840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(lean_object* v_t_3842_){
_start:
{
if (lean_obj_tag(v_t_3842_) == 0)
{
lean_object* v_size_3843_; lean_object* v_k_3844_; lean_object* v_v_3845_; lean_object* v_l_3846_; lean_object* v_r_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3857_; 
v_size_3843_ = lean_ctor_get(v_t_3842_, 0);
v_k_3844_ = lean_ctor_get(v_t_3842_, 1);
v_v_3845_ = lean_ctor_get(v_t_3842_, 2);
v_l_3846_ = lean_ctor_get(v_t_3842_, 3);
v_r_3847_ = lean_ctor_get(v_t_3842_, 4);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_t_3842_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3849_ = v_t_3842_;
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_r_3847_);
lean_inc(v_l_3846_);
lean_inc(v_v_3845_);
lean_inc(v_k_3844_);
lean_inc(v_size_3843_);
lean_dec(v_t_3842_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3855_; 
v___x_3851_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_v_3845_);
v___x_3852_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_l_3846_);
v___x_3853_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_r_3847_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 4, v___x_3853_);
lean_ctor_set(v___x_3849_, 3, v___x_3852_);
lean_ctor_set(v___x_3849_, 2, v___x_3851_);
v___x_3855_ = v___x_3849_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_size_3843_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_k_3844_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_box(1);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(lean_object* v_map_3859_){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4_spec__5(v_map_3859_);
v___x_3861_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(lean_object* v_k_3862_, lean_object* v_x_3863_){
_start:
{
if (lean_obj_tag(v_x_3863_) == 0)
{
lean_object* v___x_3864_; 
lean_dec_ref(v_k_3862_);
v___x_3864_ = lean_box(0);
return v___x_3864_;
}
else
{
lean_object* v_val_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_val_3865_ = lean_ctor_get(v_x_3863_, 0);
lean_inc(v_val_3865_);
lean_dec_ref_known(v_x_3863_, 1);
v___x_3866_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3_spec__4(v_val_3865_);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v_k_3862_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = lean_box(0);
v___x_3869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
return v___x_3869_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instToJsonConfig_toJson(lean_object* v_x_3872_){
_start:
{
lean_object* v_challenge__module_3873_; lean_object* v_solution__module_3874_; lean_object* v_theorem__names_3875_; lean_object* v_definition__names_3876_; lean_object* v_permitted__axioms_3877_; lean_object* v_enable__nanoda_x3f_3878_; lean_object* v_external__kernels_x3f_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_challenge__module_3873_ = lean_ctor_get(v_x_3872_, 0);
lean_inc_ref(v_challenge__module_3873_);
v_solution__module_3874_ = lean_ctor_get(v_x_3872_, 1);
lean_inc_ref(v_solution__module_3874_);
v_theorem__names_3875_ = lean_ctor_get(v_x_3872_, 2);
lean_inc_ref(v_theorem__names_3875_);
v_definition__names_3876_ = lean_ctor_get(v_x_3872_, 3);
lean_inc(v_definition__names_3876_);
v_permitted__axioms_3877_ = lean_ctor_get(v_x_3872_, 4);
lean_inc_ref(v_permitted__axioms_3877_);
v_enable__nanoda_x3f_3878_ = lean_ctor_get(v_x_3872_, 5);
lean_inc(v_enable__nanoda_x3f_3878_);
v_external__kernels_x3f_3879_ = lean_ctor_get(v_x_3872_, 6);
lean_inc(v_external__kernels_x3f_3879_);
lean_dec_ref(v_x_3872_);
v___x_3880_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__0));
v___x_3881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3881_, 0, v_challenge__module_3873_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3880_);
lean_ctor_set(v___x_3882_, 1, v___x_3881_);
v___x_3883_ = lean_box(0);
v___x_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3882_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__13));
v___x_3886_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_solution__module_3874_);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
lean_ctor_set(v___x_3888_, 1, v___x_3883_);
v___x_3889_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__18));
v___x_3890_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_theorem__names_3875_);
v___x_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v___x_3883_);
v___x_3893_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__23));
v___x_3894_ = l_Lean_Option_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__1(v_definition__names_3876_);
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3893_);
lean_ctor_set(v___x_3895_, 1, v___x_3894_);
v___x_3896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
lean_ctor_set(v___x_3896_, 1, v___x_3883_);
v___x_3897_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runExternalKernel___lam__0___closed__11));
v___x_3898_ = l_Lean_Array_toJson___at___00Lake_Check_instToJsonConfig_toJson_spec__0(v_permitted__axioms_3877_);
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
lean_ctor_set(v___x_3900_, 1, v___x_3883_);
v___x_3901_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__32));
v___x_3902_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__2(v___x_3901_, v_enable__nanoda_x3f_3878_);
lean_dec(v_enable__nanoda_x3f_3878_);
v___x_3903_ = ((lean_object*)(l_Lake_Check_instFromJsonConfig_fromJson___closed__38));
v___x_3904_ = l_Lean_Json_opt___at___00Lake_Check_instToJsonConfig_toJson_spec__3(v___x_3903_, v_external__kernels_x3f_3879_);
v___x_3905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
lean_ctor_set(v___x_3905_, 1, v___x_3883_);
v___x_3906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3902_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3900_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3896_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3892_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3888_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
v___x_3911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3884_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = ((lean_object*)(l_Lake_Check_instToJsonConfig_toJson___closed__0));
v___x_3913_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lake_Check_instToJsonConfig_toJson_spec__4(v___x_3911_, v___x_3912_);
v___x_3914_ = l_Lean_Json_mkObj(v___x_3913_);
lean_dec(v___x_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(lean_object* v_x_3923_, lean_object* v_x_3924_){
_start:
{
if (lean_obj_tag(v_x_3923_) == 0)
{
lean_object* v___x_3925_; 
v___x_3925_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_3925_;
}
else
{
lean_object* v_val_3926_; lean_object* v___x_3927_; uint8_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_val_3926_ = lean_ctor_get(v_x_3923_, 0);
v___x_3927_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_3928_ = lean_unbox(v_val_3926_);
v___x_3929_ = l_Bool_repr___redArg(v___x_3928_);
v___x_3930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3927_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l_Repr_addAppParen(v___x_3930_, v_x_3924_);
return v___x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___boxed(lean_object* v_x_3932_, lean_object* v_x_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_x_3932_, v_x_3933_);
lean_dec(v_x_3933_);
lean_dec(v_x_3932_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_Check_instReprConfig_repr_spec__4(lean_object* v_a_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_nat_to_int(v_a_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(lean_object* v_x_3937_, lean_object* v_x_3938_, lean_object* v_x_3939_){
_start:
{
if (lean_obj_tag(v_x_3939_) == 0)
{
lean_dec(v_x_3937_);
return v_x_3938_;
}
else
{
lean_object* v_head_3940_; lean_object* v_tail_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3952_; 
v_head_3940_ = lean_ctor_get(v_x_3939_, 0);
v_tail_3941_ = lean_ctor_get(v_x_3939_, 1);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_x_3939_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3943_ = v_x_3939_;
v_isShared_3944_ = v_isSharedCheck_3952_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_tail_3941_);
lean_inc(v_head_3940_);
lean_dec(v_x_3939_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3952_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
lean_inc(v_x_3937_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set_tag(v___x_3943_, 5);
lean_ctor_set(v___x_3943_, 1, v_x_3937_);
lean_ctor_set(v___x_3943_, 0, v_x_3938_);
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_x_3938_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_x_3937_);
v___x_3946_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = l_String_quote(v_head_3940_);
v___x_3948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
v___x_3949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3946_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v_x_3938_ = v___x_3949_;
v_x_3939_ = v_tail_3941_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_3953_, lean_object* v_x_3954_, lean_object* v_x_3955_){
_start:
{
if (lean_obj_tag(v_x_3955_) == 0)
{
lean_dec(v_x_3953_);
return v_x_3954_;
}
else
{
lean_object* v_head_3956_; lean_object* v_tail_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3968_; 
v_head_3956_ = lean_ctor_get(v_x_3955_, 0);
v_tail_3957_ = lean_ctor_get(v_x_3955_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_x_3955_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3959_ = v_x_3955_;
v_isShared_3960_ = v_isSharedCheck_3968_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_tail_3957_);
lean_inc(v_head_3956_);
lean_dec(v_x_3955_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3968_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
lean_inc(v_x_3953_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 5);
lean_ctor_set(v___x_3959_, 1, v_x_3953_);
lean_ctor_set(v___x_3959_, 0, v_x_3954_);
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_x_3954_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_x_3953_);
v___x_3962_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3963_ = l_String_quote(v_head_3956_);
v___x_3964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
v___x_3965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3962_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3_spec__6(v_x_3953_, v___x_3965_, v_tail_3957_);
return v___x_3966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = l_String_quote(v___y_3969_);
v___x_3971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(lean_object* v_x_3972_, lean_object* v_x_3973_){
_start:
{
if (lean_obj_tag(v_x_3972_) == 0)
{
lean_object* v___x_3974_; 
lean_dec(v_x_3973_);
v___x_3974_ = lean_box(0);
return v___x_3974_;
}
else
{
lean_object* v_tail_3975_; 
v_tail_3975_ = lean_ctor_get(v_x_3972_, 1);
if (lean_obj_tag(v_tail_3975_) == 0)
{
lean_object* v_head_3976_; lean_object* v___x_3977_; 
lean_dec(v_x_3973_);
v_head_3976_ = lean_ctor_get(v_x_3972_, 0);
lean_inc(v_head_3976_);
lean_dec_ref_known(v_x_3972_, 2);
v___x_3977_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3976_);
return v___x_3977_;
}
else
{
lean_object* v_head_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_inc(v_tail_3975_);
v_head_3978_ = lean_ctor_get(v_x_3972_, 0);
lean_inc(v_head_3978_);
lean_dec_ref_known(v_x_3972_, 2);
v___x_3979_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0___lam__0(v_head_3978_);
v___x_3980_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0_spec__3(v_x_3973_, v___x_3979_, v_tail_3975_);
return v___x_3980_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__0));
v___x_3989_ = lean_string_length(v___x_3988_);
return v___x_3989_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__4);
v___x_3991_ = lean_nat_to_int(v___x_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(lean_object* v_xs_3999_){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_4000_ = lean_array_get_size(v_xs_3999_);
v___x_4001_ = lean_unsigned_to_nat(0u);
v___x_4002_ = lean_nat_dec_eq(v___x_4000_, v___x_4001_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4003_ = lean_array_to_list(v_xs_3999_);
v___x_4004_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_4005_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0_spec__0(v___x_4003_, v___x_4004_);
v___x_4006_ = lean_obj_once(&l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5, &l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__5);
v___x_4007_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__6));
v___x_4008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
lean_ctor_set(v___x_4008_, 1, v___x_4005_);
v___x_4009_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_4010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4008_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
v___x_4011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4006_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = l_Std_Format_fill(v___x_4011_);
return v___x_4012_;
}
else
{
lean_object* v___x_4013_; 
lean_dec_ref(v_xs_3999_);
v___x_4013_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__9));
return v___x_4013_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(lean_object* v_x_4014_, lean_object* v_x_4015_){
_start:
{
if (lean_obj_tag(v_x_4014_) == 0)
{
lean_object* v___x_4016_; 
v___x_4016_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_4016_;
}
else
{
lean_object* v_val_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_val_4017_ = lean_ctor_get(v_x_4014_, 0);
lean_inc(v_val_4017_);
lean_dec_ref_known(v_x_4014_, 1);
v___x_4018_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_4019_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_val_4017_);
v___x_4020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4018_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = l_Repr_addAppParen(v___x_4020_, v_x_4015_);
return v___x_4021_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1___boxed(lean_object* v_x_4022_, lean_object* v_x_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_x_4022_, v_x_4023_);
lean_dec(v_x_4023_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(lean_object* v_init_4025_, lean_object* v_x_4026_){
_start:
{
if (lean_obj_tag(v_x_4026_) == 0)
{
lean_object* v_k_4027_; lean_object* v_v_4028_; lean_object* v_l_4029_; lean_object* v_r_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v_k_4027_ = lean_ctor_get(v_x_4026_, 1);
v_v_4028_ = lean_ctor_get(v_x_4026_, 2);
v_l_4029_ = lean_ctor_get(v_x_4026_, 3);
v_r_4030_ = lean_ctor_get(v_x_4026_, 4);
v___x_4031_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_4025_, v_r_4030_);
lean_inc(v_v_4028_);
lean_inc(v_k_4027_);
v___x_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4032_, 0, v_k_4027_);
lean_ctor_set(v___x_4032_, 1, v_v_4028_);
v___x_4033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
lean_ctor_set(v___x_4033_, 1, v___x_4031_);
v_init_4025_ = v___x_4033_;
v_x_4026_ = v_l_4029_;
goto _start;
}
else
{
return v_init_4025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4___boxed(lean_object* v_init_4035_, lean_object* v_x_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v_init_4035_, v_x_4036_);
lean_dec(v_x_4036_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(lean_object* v_x_4038_, lean_object* v_x_4039_, lean_object* v_x_4040_){
_start:
{
if (lean_obj_tag(v_x_4040_) == 0)
{
lean_dec(v_x_4038_);
return v_x_4039_;
}
else
{
lean_object* v_head_4041_; lean_object* v_tail_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4051_; 
v_head_4041_ = lean_ctor_get(v_x_4040_, 0);
v_tail_4042_ = lean_ctor_get(v_x_4040_, 1);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_x_4040_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4044_ = v_x_4040_;
v_isShared_4045_ = v_isSharedCheck_4051_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_tail_4042_);
lean_inc(v_head_4041_);
lean_dec(v_x_4040_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4051_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
lean_inc(v_x_4038_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set_tag(v___x_4044_, 5);
lean_ctor_set(v___x_4044_, 1, v_x_4038_);
lean_ctor_set(v___x_4044_, 0, v_x_4039_);
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_x_4039_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_x_4038_);
v___x_4047_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
lean_ctor_set(v___x_4048_, 1, v_head_4041_);
v_x_4039_ = v___x_4048_;
v_x_4040_ = v_tail_4042_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(lean_object* v_x_4052_, lean_object* v_x_4053_){
_start:
{
if (lean_obj_tag(v_x_4052_) == 0)
{
lean_object* v___x_4054_; 
lean_dec(v_x_4053_);
v___x_4054_ = lean_box(0);
return v___x_4054_;
}
else
{
lean_object* v_tail_4055_; 
v_tail_4055_ = lean_ctor_get(v_x_4052_, 1);
if (lean_obj_tag(v_tail_4055_) == 0)
{
lean_object* v_head_4056_; 
lean_dec(v_x_4053_);
v_head_4056_ = lean_ctor_get(v_x_4052_, 0);
lean_inc(v_head_4056_);
lean_dec_ref_known(v_x_4052_, 2);
return v_head_4056_;
}
else
{
lean_object* v_head_4057_; lean_object* v___x_4058_; 
lean_inc(v_tail_4055_);
v_head_4057_ = lean_ctor_get(v_x_4052_, 0);
lean_inc(v_head_4057_);
lean_dec_ref_known(v_x_4052_, 2);
v___x_4058_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10_spec__11(v_x_4053_, v_head_4057_, v_tail_4055_);
return v___x_4058_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__0));
v___x_4062_ = lean_string_length(v___x_4061_);
return v___x_4062_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__2);
v___x_4064_ = lean_nat_to_int(v___x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(lean_object* v_x_4069_){
_start:
{
lean_object* v_fst_4070_; lean_object* v_snd_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4094_; 
v_fst_4070_ = lean_ctor_get(v_x_4069_, 0);
v_snd_4071_ = lean_ctor_get(v_x_4069_, 1);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_x_4069_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4073_ = v_x_4069_;
v_isShared_4074_ = v_isSharedCheck_4094_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_snd_4071_);
lean_inc(v_fst_4070_);
lean_dec(v_x_4069_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4094_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4075_ = l_String_quote(v_fst_4070_);
v___x_4076_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
v___x_4077_ = lean_box(0);
if (v_isShared_4074_ == 0)
{
lean_ctor_set_tag(v___x_4073_, 1);
lean_ctor_set(v___x_4073_, 1, v___x_4077_);
lean_ctor_set(v___x_4073_, 0, v___x_4076_);
v___x_4079_ = v___x_4073_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; 
v___x_4080_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_snd_4071_);
v___x_4081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4079_);
v___x_4082_ = l_List_reverse___redArg(v___x_4081_);
v___x_4083_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_4084_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8_spec__10(v___x_4082_, v___x_4083_);
v___x_4085_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__3);
v___x_4086_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__4));
v___x_4087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
lean_ctor_set(v___x_4087_, 1, v___x_4084_);
v___x_4088_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg___closed__5));
v___x_4089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4085_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = 0;
v___x_4092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set_uint8(v___x_4092_, sizeof(void*)*1, v___x_4091_);
return v___x_4092_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(lean_object* v_x_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_){
_start:
{
if (lean_obj_tag(v_x_4097_) == 0)
{
lean_dec(v_x_4095_);
return v_x_4096_;
}
else
{
lean_object* v_head_4098_; lean_object* v_tail_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4109_; 
v_head_4098_ = lean_ctor_get(v_x_4097_, 0);
v_tail_4099_ = lean_ctor_get(v_x_4097_, 1);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_x_4097_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4101_ = v_x_4097_;
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_tail_4099_);
lean_inc(v_head_4098_);
lean_dec(v_x_4097_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4109_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
lean_inc(v_x_4095_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set_tag(v___x_4101_, 5);
lean_ctor_set(v___x_4101_, 1, v_x_4095_);
lean_ctor_set(v___x_4101_, 0, v_x_4096_);
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_x_4096_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_x_4095_);
v___x_4104_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4098_);
v___x_4106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v_x_4096_ = v___x_4106_;
v_x_4097_ = v_tail_4099_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(lean_object* v_x_4110_, lean_object* v_x_4111_, lean_object* v_x_4112_){
_start:
{
if (lean_obj_tag(v_x_4112_) == 0)
{
lean_dec(v_x_4110_);
return v_x_4111_;
}
else
{
lean_object* v_head_4113_; lean_object* v_tail_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4124_; 
v_head_4113_ = lean_ctor_get(v_x_4112_, 0);
v_tail_4114_ = lean_ctor_get(v_x_4112_, 1);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_x_4112_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4116_ = v_x_4112_;
v_isShared_4117_ = v_isSharedCheck_4124_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_tail_4114_);
lean_inc(v_head_4113_);
lean_dec(v_x_4112_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4124_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
lean_inc(v_x_4110_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 5);
lean_ctor_set(v___x_4116_, 1, v_x_4110_);
lean_ctor_set(v___x_4116_, 0, v_x_4111_);
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_x_4111_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v_x_4110_);
v___x_4119_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4120_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4113_);
v___x_4121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4119_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12_spec__14(v_x_4110_, v___x_4121_, v_tail_4114_);
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(lean_object* v_x_4125_, lean_object* v_x_4126_){
_start:
{
if (lean_obj_tag(v_x_4125_) == 0)
{
lean_object* v___x_4127_; 
lean_dec(v_x_4126_);
v___x_4127_ = lean_box(0);
return v___x_4127_;
}
else
{
lean_object* v_tail_4128_; 
v_tail_4128_ = lean_ctor_get(v_x_4125_, 1);
if (lean_obj_tag(v_tail_4128_) == 0)
{
lean_object* v_head_4129_; lean_object* v___x_4130_; 
lean_dec(v_x_4126_);
v_head_4129_ = lean_ctor_get(v_x_4125_, 0);
lean_inc(v_head_4129_);
lean_dec_ref_known(v_x_4125_, 2);
v___x_4130_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4129_);
return v___x_4130_;
}
else
{
lean_object* v_head_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_inc(v_tail_4128_);
v_head_4131_ = lean_ctor_get(v_x_4125_, 0);
lean_inc(v_head_4131_);
lean_dec_ref_known(v_x_4125_, 2);
v___x_4132_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_head_4131_);
v___x_4133_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9_spec__12(v_x_4126_, v___x_4132_, v_tail_4128_);
return v___x_4133_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = ((lean_object*)(l_List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0___closed__1));
v___x_4137_ = lean_string_length(v___x_4136_);
return v___x_4137_;
}
}
static lean_object* _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__1);
v___x_4139_ = lean_nat_to_int(v___x_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(lean_object* v_a_4142_){
_start:
{
if (lean_obj_tag(v_a_4142_) == 0)
{
lean_object* v___x_4143_; 
v___x_4143_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__0));
return v___x_4143_;
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; uint8_t v___x_4152_; lean_object* v___x_4153_; 
v___x_4144_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__3));
v___x_4145_ = l_Std_Format_joinSep___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__9(v_a_4142_, v___x_4144_);
v___x_4146_ = lean_obj_once(&l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2, &l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2_once, _init_l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__2);
v___x_4147_ = ((lean_object*)(l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg___closed__3));
v___x_4148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
lean_ctor_set(v___x_4148_, 1, v___x_4145_);
v___x_4149_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__7));
v___x_4150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4148_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4146_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
v___x_4152_ = 0;
v___x_4153_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4153_, 0, v___x_4151_);
lean_ctor_set_uint8(v___x_4153_, sizeof(void*)*1, v___x_4152_);
return v___x_4153_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(lean_object* v_x_4157_, lean_object* v_x_4158_){
_start:
{
if (lean_obj_tag(v_x_4157_) == 0)
{
lean_object* v___x_4159_; 
v___x_4159_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__1));
return v___x_4159_;
}
else
{
lean_object* v_val_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_val_4160_ = lean_ctor_get(v_x_4157_, 0);
v___x_4161_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2___closed__3));
v___x_4162_ = lean_unsigned_to_nat(1024u);
v___x_4163_ = ((lean_object*)(l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___closed__1));
v___x_4164_ = lean_box(0);
v___x_4165_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__4(v___x_4164_, v_val_4160_);
v___x_4166_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v___x_4165_);
v___x_4167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4163_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Repr_addAppParen(v___x_4167_, v___x_4162_);
v___x_4169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4161_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = l_Repr_addAppParen(v___x_4169_, v_x_4158_);
return v___x_4170_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3___boxed(lean_object* v_x_4171_, lean_object* v_x_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_x_4171_, v_x_4172_);
lean_dec(v_x_4172_);
lean_dec(v_x_4171_);
return v_res_4173_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = lean_unsigned_to_nat(20u);
v___x_4187_ = lean_nat_to_int(v___x_4186_);
return v___x_4187_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_unsigned_to_nat(19u);
v___x_4191_ = lean_nat_to_int(v___x_4190_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = lean_unsigned_to_nat(17u);
v___x_4195_ = lean_nat_to_int(v___x_4194_);
return v___x_4195_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = lean_unsigned_to_nat(18u);
v___x_4203_ = lean_nat_to_int(v___x_4202_);
return v___x_4203_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4206_ = lean_unsigned_to_nat(21u);
v___x_4207_ = lean_nat_to_int(v___x_4206_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4209_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__0));
v___x_4210_ = lean_string_length(v___x_4209_);
return v___x_4210_;
}
}
static lean_object* _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__18, &l_Lake_Check_instReprConfig_repr___redArg___closed__18_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__18);
v___x_4212_ = lean_nat_to_int(v___x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___redArg(lean_object* v_x_4217_){
_start:
{
lean_object* v_challenge__module_4218_; lean_object* v_solution__module_4219_; lean_object* v_theorem__names_4220_; lean_object* v_definition__names_4221_; lean_object* v_permitted__axioms_4222_; lean_object* v_enable__nanoda_x3f_4223_; lean_object* v_external__kernels_x3f_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; uint8_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_challenge__module_4218_ = lean_ctor_get(v_x_4217_, 0);
lean_inc_ref(v_challenge__module_4218_);
v_solution__module_4219_ = lean_ctor_get(v_x_4217_, 1);
lean_inc_ref(v_solution__module_4219_);
v_theorem__names_4220_ = lean_ctor_get(v_x_4217_, 2);
lean_inc_ref(v_theorem__names_4220_);
v_definition__names_4221_ = lean_ctor_get(v_x_4217_, 3);
lean_inc(v_definition__names_4221_);
v_permitted__axioms_4222_ = lean_ctor_get(v_x_4217_, 4);
lean_inc_ref(v_permitted__axioms_4222_);
v_enable__nanoda_x3f_4223_ = lean_ctor_get(v_x_4217_, 5);
lean_inc(v_enable__nanoda_x3f_4223_);
v_external__kernels_x3f_4224_ = lean_ctor_get(v_x_4217_, 6);
lean_inc(v_external__kernels_x3f_4224_);
lean_dec_ref(v_x_4217_);
v___x_4225_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__4));
v___x_4226_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__5));
v___x_4227_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__6, &l_Lake_Check_instReprConfig_repr___redArg___closed__6_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__6);
v___x_4228_ = l_String_quote(v_challenge__module_4218_);
v___x_4229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
v___x_4230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4227_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = 0;
v___x_4232_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set_uint8(v___x_4232_, sizeof(void*)*1, v___x_4231_);
v___x_4233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4226_);
lean_ctor_set(v___x_4233_, 1, v___x_4232_);
v___x_4234_ = ((lean_object*)(l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0___closed__2));
v___x_4235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4233_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
v___x_4236_ = lean_box(1);
v___x_4237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4237_, 0, v___x_4235_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__7));
v___x_4239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
lean_ctor_set(v___x_4240_, 1, v___x_4225_);
v___x_4241_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__8, &l_Lake_Check_instReprConfig_repr___redArg___closed__8_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__8);
v___x_4242_ = l_String_quote(v_solution__module_4219_);
v___x_4243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4241_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
lean_ctor_set_uint8(v___x_4245_, sizeof(void*)*1, v___x_4231_);
v___x_4246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4240_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
lean_ctor_set(v___x_4247_, 1, v___x_4234_);
v___x_4248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
lean_ctor_set(v___x_4248_, 1, v___x_4236_);
v___x_4249_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__9));
v___x_4250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
lean_ctor_set(v___x_4251_, 1, v___x_4225_);
v___x_4252_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__10, &l_Lake_Check_instReprConfig_repr___redArg___closed__10_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__10);
v___x_4253_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_theorem__names_4220_);
v___x_4254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4252_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
lean_ctor_set_uint8(v___x_4255_, sizeof(void*)*1, v___x_4231_);
v___x_4256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4251_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
lean_ctor_set(v___x_4257_, 1, v___x_4234_);
v___x_4258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
lean_ctor_set(v___x_4258_, 1, v___x_4236_);
v___x_4259_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__11));
v___x_4260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
lean_ctor_set(v___x_4261_, 1, v___x_4225_);
v___x_4262_ = lean_unsigned_to_nat(0u);
v___x_4263_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__1(v_definition__names_4221_, v___x_4262_);
v___x_4264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4227_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
lean_ctor_set_uint8(v___x_4265_, sizeof(void*)*1, v___x_4231_);
v___x_4266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4261_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
lean_ctor_set(v___x_4267_, 1, v___x_4234_);
v___x_4268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
lean_ctor_set(v___x_4268_, 1, v___x_4236_);
v___x_4269_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__12));
v___x_4270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4268_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
lean_ctor_set(v___x_4271_, 1, v___x_4225_);
v___x_4272_ = l_Array_repr___at___00Lake_Check_instReprConfig_repr_spec__0(v_permitted__axioms_4222_);
v___x_4273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4227_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
lean_ctor_set_uint8(v___x_4274_, sizeof(void*)*1, v___x_4231_);
v___x_4275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4271_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
lean_ctor_set(v___x_4276_, 1, v___x_4234_);
v___x_4277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
lean_ctor_set(v___x_4277_, 1, v___x_4236_);
v___x_4278_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__13));
v___x_4279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
lean_ctor_set(v___x_4280_, 1, v___x_4225_);
v___x_4281_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__14, &l_Lake_Check_instReprConfig_repr___redArg___closed__14_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__14);
v___x_4282_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__2(v_enable__nanoda_x3f_4223_, v___x_4262_);
lean_dec(v_enable__nanoda_x3f_4223_);
v___x_4283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4281_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4284_, 0, v___x_4283_);
lean_ctor_set_uint8(v___x_4284_, sizeof(void*)*1, v___x_4231_);
v___x_4285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4280_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
lean_ctor_set(v___x_4286_, 1, v___x_4234_);
v___x_4287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
lean_ctor_set(v___x_4287_, 1, v___x_4236_);
v___x_4288_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__15));
v___x_4289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4287_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
lean_ctor_set(v___x_4290_, 1, v___x_4225_);
v___x_4291_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__16, &l_Lake_Check_instReprConfig_repr___redArg___closed__16_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__16);
v___x_4292_ = l_Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3(v_external__kernels_x3f_4224_, v___x_4262_);
lean_dec(v_external__kernels_x3f_4224_);
v___x_4293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set_uint8(v___x_4294_, sizeof(void*)*1, v___x_4231_);
v___x_4295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4290_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = lean_obj_once(&l_Lake_Check_instReprConfig_repr___redArg___closed__19, &l_Lake_Check_instReprConfig_repr___redArg___closed__19_once, _init_l_Lake_Check_instReprConfig_repr___redArg___closed__19);
v___x_4297_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__20));
v___x_4298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
lean_ctor_set(v___x_4298_, 1, v___x_4295_);
v___x_4299_ = ((lean_object*)(l_Lake_Check_instReprConfig_repr___redArg___closed__21));
v___x_4300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4296_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
lean_ctor_set_uint8(v___x_4302_, sizeof(void*)*1, v___x_4231_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr(lean_object* v_x_4303_, lean_object* v_prec_4304_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_Lake_Check_instReprConfig_repr___redArg(v_x_4303_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_instReprConfig_repr___boxed(lean_object* v_x_4306_, lean_object* v_prec_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_Lake_Check_instReprConfig_repr(v_x_4306_, v_prec_4307_);
lean_dec(v_prec_4307_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(lean_object* v_a_4309_, lean_object* v_n_4310_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___redArg(v_a_4309_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5___boxed(lean_object* v_a_4312_, lean_object* v_n_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5(v_a_4312_, v_n_4313_);
lean_dec(v_n_4313_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(lean_object* v_x_4315_, lean_object* v_x_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___redArg(v_x_4315_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8___boxed(lean_object* v_x_4318_, lean_object* v_x_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Prod_repr___at___00List_repr___at___00Option_repr___at___00Lake_Check_instReprConfig_repr_spec__3_spec__5_spec__8(v_x_4318_, v_x_4319_);
lean_dec(v_x_4319_);
return v_res_4320_;
}
}
lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(lean_object* v_s_4323_){
_start:
{
uint32_t v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = 10;
v___x_4326_ = lean_string_push(v_s_4323_, v___x_4325_);
v___x_4327_ = l_IO_eprint___at___00__private_Lake_CLI_Check_0__Lake_Check_runSandBoxedWithStdoutTo_spec__0(v___x_4326_);
return v___x_4327_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4323_ = stack[0].m_obj;
lean_object* v_res_4328_;
v_res_4328_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_4323_);
stack->m_obj
 = v_res_4328_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0___boxed(lean_object* v_s_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v_s_4329_);
return v_res_4331_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1(void){
_start:
{
uint32_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = 2;
v___x_4334_ = lean_box_uint32(v___x_4333_);
return v___x_4334_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(lean_object* v_msg_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_4338_ = lean_string_append(v___x_4337_, v_msg_4335_);
v___x_4339_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_4338_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4347_; 
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4347_ == 0)
{
lean_object* v_unused_4348_; 
v_unused_4348_ = lean_ctor_get(v___x_4339_, 0);
lean_dec(v_unused_4348_);
v___x_4341_ = v___x_4339_;
v_isShared_4342_ = v_isSharedCheck_4347_;
goto v_resetjp_4340_;
}
else
{
lean_dec(v___x_4339_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4347_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4343_; lean_object* v___x_4345_; 
v___x_4343_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed__const__1;
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v___x_4343_);
v___x_4345_ = v___x_4341_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
v_a_4349_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4339_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4339_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_cannotRun_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4335_ = stack[0].m_obj;
lean_object* v_res_4357_;
v_res_4357_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_4335_);
stack->m_obj
 = v_res_4357_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___boxed(lean_object* v_msg_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v_msg_4358_);
lean_dec_ref(v_msg_4358_);
return v_res_4360_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(lean_object* v_cmd_4364_, lean_object* v_projectDir_4365_){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; uint8_t v___x_4369_; 
v___x_4367_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__0));
lean_inc_ref(v_projectDir_4365_);
v___x_4368_ = l_System_FilePath_join(v_projectDir_4365_, v___x_4367_);
v___x_4369_ = l_System_FilePath_pathExists(v___x_4368_);
lean_dec_ref(v___x_4368_);
if (v___x_4369_ == 0)
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4370_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_4371_ = lean_string_append(v___x_4370_, v_projectDir_4365_);
lean_dec_ref(v_projectDir_4365_);
v___x_4372_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__1));
v___x_4373_ = lean_string_append(v___x_4371_, v___x_4372_);
v___x_4374_ = lean_string_append(v___x_4373_, v_cmd_4364_);
v___x_4375_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___closed__2));
v___x_4376_ = lean_string_append(v___x_4374_, v___x_4375_);
v___x_4377_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4376_);
lean_dec_ref(v___x_4376_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4386_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4384_; 
v___x_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4382_, 0, v_a_4378_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4382_);
v___x_4384_ = v___x_4380_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
v_a_4387_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4377_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4377_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
else
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
lean_dec_ref(v_projectDir_4365_);
v___x_4395_ = lean_box(0);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_checkManifest_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_4364_ = stack[0].m_obj;
lean_object* v_projectDir_4365_ = stack[1].m_obj;
lean_object* v_res_4397_;
v_res_4397_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_4364_, v_projectDir_4365_);
stack->m_obj
 = v_res_4397_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkManifest___boxed(lean_object* v_cmd_4398_, lean_object* v_projectDir_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v_cmd_4398_, v_projectDir_4399_);
lean_dec_ref(v_cmd_4398_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(lean_object* v_lean_4402_, lean_object* v_name_4403_){
_start:
{
lean_object* v_binDir_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_binDir_4404_ = lean_ctor_get(v_lean_4402_, 6);
lean_inc_ref(v_binDir_4404_);
lean_dec_ref(v_lean_4402_);
v___x_4405_ = l_System_FilePath_join(v_binDir_4404_, v_name_4403_);
v___x_4406_ = l_System_FilePath_exeExtension;
v___x_4407_ = l_System_FilePath_addExtension(v___x_4405_, v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(lean_object* v_lean_4416_){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4417_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__0));
v___x_4418_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__1));
lean_inc_ref_n(v_lean_4416_, 4);
v___x_4419_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4416_, v___x_4418_);
v___x_4420_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__0));
v___x_4421_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_4422_ = lean_unsigned_to_nat(3u);
v___x_4423_ = lean_mk_empty_array_with_capacity(v___x_4422_);
v___x_4424_ = lean_array_push(v___x_4423_, v___x_4419_);
v___x_4425_ = lean_array_push(v___x_4424_, v___x_4420_);
v___x_4426_ = lean_array_push(v___x_4425_, v___x_4421_);
v___x_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4417_);
lean_ctor_set(v___x_4427_, 1, v___x_4426_);
v___x_4428_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__2));
v___x_4429_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4416_, v___x_4428_);
v___x_4430_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__3));
v___x_4431_ = lean_unsigned_to_nat(2u);
v___x_4432_ = lean_mk_empty_array_with_capacity(v___x_4431_);
v___x_4433_ = lean_array_push(v___x_4432_, v___x_4429_);
v___x_4434_ = lean_array_push(v___x_4433_, v___x_4430_);
v___x_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4428_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
v___x_4436_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_4437_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__5));
v___x_4438_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4416_, v___x_4437_);
v___x_4439_ = lean_unsigned_to_nat(1u);
v___x_4440_ = lean_mk_empty_array_with_capacity(v___x_4439_);
lean_inc_ref_n(v___x_4440_, 2);
v___x_4441_ = lean_array_push(v___x_4440_, v___x_4438_);
v___x_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4436_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
v___x_4443_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__6));
v___x_4444_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4416_, v___x_4443_);
v___x_4445_ = lean_array_push(v___x_4440_, v___x_4444_);
v___x_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4443_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
v___x_4447_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__7));
v___x_4448_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___lam__0(v_lean_4416_, v___x_4447_);
v___x_4449_ = lean_array_push(v___x_4440_, v___x_4448_);
v___x_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4447_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
v___x_4451_ = lean_unsigned_to_nat(5u);
v___x_4452_ = lean_mk_empty_array_with_capacity(v___x_4451_);
v___x_4453_ = lean_array_push(v___x_4452_, v___x_4427_);
v___x_4454_ = lean_array_push(v___x_4453_, v___x_4435_);
v___x_4455_ = lean_array_push(v___x_4454_, v___x_4442_);
v___x_4456_ = lean_array_push(v___x_4455_, v___x_4446_);
v___x_4457_ = lean_array_push(v___x_4456_, v___x_4450_);
return v___x_4457_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(uint8_t v_a_4458_, lean_object* v_b_4459_, lean_object* v_x_4460_){
_start:
{
if (lean_obj_tag(v_x_4460_) == 0)
{
lean_dec(v_b_4459_);
return v_x_4460_;
}
else
{
lean_object* v_key_4461_; lean_object* v_value_4462_; lean_object* v_tail_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4479_; 
v_key_4461_ = lean_ctor_get(v_x_4460_, 0);
v_value_4462_ = lean_ctor_get(v_x_4460_, 1);
v_tail_4463_ = lean_ctor_get(v_x_4460_, 2);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_x_4460_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4465_ = v_x_4460_;
v_isShared_4466_ = v_isSharedCheck_4479_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_tail_4463_);
lean_inc(v_value_4462_);
lean_inc(v_key_4461_);
lean_dec(v_x_4460_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4479_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; uint8_t v___x_4470_; 
v___x_4467_ = lean_obj_tag_nat(v_key_4461_);
v___x_4468_ = lean_box(v_a_4458_);
v___x_4469_ = lean_obj_tag_nat(v___x_4468_);
lean_dec(v___x_4468_);
v___x_4470_ = lean_nat_dec_eq(v___x_4467_, v___x_4469_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4471_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4458_, v_b_4459_, v_tail_4463_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 2, v___x_4471_);
v___x_4473_ = v___x_4465_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_key_4461_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v_value_4462_);
lean_ctor_set(v_reuseFailAlloc_4474_, 2, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4477_; 
lean_dec(v_value_4462_);
lean_dec(v_key_4461_);
v___x_4475_ = lean_box(v_a_4458_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 1, v_b_4459_);
lean_ctor_set(v___x_4465_, 0, v___x_4475_);
v___x_4477_ = v___x_4465_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_b_4459_);
lean_ctor_set(v_reuseFailAlloc_4478_, 2, v_tail_4463_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_4458_ = stack[0].m_num;
lean_object* v_b_4459_ = stack[1].m_obj;
lean_object* v_x_4460_ = stack[2].m_obj;
lean_object* v_res_4480_;
v_res_4480_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4458_, v_b_4459_, v_x_4460_);
stack->m_obj
 = v_res_4480_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg___boxed(lean_object* v_a_4481_, lean_object* v_b_4482_, lean_object* v_x_4483_){
_start:
{
uint8_t v_a_boxed_4484_; lean_object* v_res_4485_; 
v_a_boxed_4484_ = lean_unbox(v_a_4481_);
v_res_4485_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_boxed_4484_, v_b_4482_, v_x_4483_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_4486_, lean_object* v_x_4487_){
_start:
{
if (lean_obj_tag(v_x_4487_) == 0)
{
return v_x_4486_;
}
else
{
lean_object* v_key_4488_; lean_object* v_value_4489_; lean_object* v_tail_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4514_; 
v_key_4488_ = lean_ctor_get(v_x_4487_, 0);
v_value_4489_ = lean_ctor_get(v_x_4487_, 1);
v_tail_4490_ = lean_ctor_get(v_x_4487_, 2);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_x_4487_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4492_ = v_x_4487_;
v_isShared_4493_ = v_isSharedCheck_4514_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_tail_4490_);
lean_inc(v_value_4489_);
lean_inc(v_key_4488_);
lean_dec(v_x_4487_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4514_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; uint8_t v___x_4495_; uint64_t v___x_4496_; uint64_t v___x_4497_; uint64_t v___x_4498_; uint64_t v_fold_4499_; uint64_t v___x_4500_; uint64_t v___x_4501_; uint64_t v___x_4502_; size_t v___x_4503_; size_t v___x_4504_; size_t v___x_4505_; size_t v___x_4506_; size_t v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4494_ = lean_array_get_size(v_x_4486_);
v___x_4495_ = lean_unbox(v_key_4488_);
v___x_4496_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v___x_4495_);
v___x_4497_ = 32ULL;
v___x_4498_ = lean_uint64_shift_right(v___x_4496_, v___x_4497_);
v_fold_4499_ = lean_uint64_xor(v___x_4496_, v___x_4498_);
v___x_4500_ = 16ULL;
v___x_4501_ = lean_uint64_shift_right(v_fold_4499_, v___x_4500_);
v___x_4502_ = lean_uint64_xor(v_fold_4499_, v___x_4501_);
v___x_4503_ = lean_uint64_to_usize(v___x_4502_);
v___x_4504_ = lean_usize_of_nat(v___x_4494_);
v___x_4505_ = ((size_t)1ULL);
v___x_4506_ = lean_usize_sub(v___x_4504_, v___x_4505_);
v___x_4507_ = lean_usize_land(v___x_4503_, v___x_4506_);
v___x_4508_ = lean_array_uget_borrowed(v_x_4486_, v___x_4507_);
lean_inc(v___x_4508_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 2, v___x_4508_);
v___x_4510_ = v___x_4492_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_key_4488_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_value_4489_);
lean_ctor_set(v_reuseFailAlloc_4513_, 2, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; 
v___x_4511_ = lean_array_uset(v_x_4486_, v___x_4507_, v___x_4510_);
v_x_4486_ = v___x_4511_;
v_x_4487_ = v_tail_4490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4515_, lean_object* v_source_4516_, lean_object* v_target_4517_){
_start:
{
lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4518_ = lean_array_get_size(v_source_4516_);
v___x_4519_ = lean_nat_dec_lt(v_i_4515_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_dec_ref(v_source_4516_);
lean_dec(v_i_4515_);
return v_target_4517_;
}
else
{
lean_object* v_es_4520_; lean_object* v___x_4521_; lean_object* v_source_4522_; lean_object* v_target_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v_es_4520_ = lean_array_fget(v_source_4516_, v_i_4515_);
v___x_4521_ = lean_box(0);
v_source_4522_ = lean_array_fset(v_source_4516_, v_i_4515_, v___x_4521_);
v_target_4523_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4517_, v_es_4520_);
v___x_4524_ = lean_unsigned_to_nat(1u);
v___x_4525_ = lean_nat_add(v_i_4515_, v___x_4524_);
lean_dec(v_i_4515_);
v_i_4515_ = v___x_4525_;
v_source_4516_ = v_source_4522_;
v_target_4517_ = v_target_4523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(lean_object* v_data_4527_){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v_nbuckets_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4528_ = lean_array_get_size(v_data_4527_);
v___x_4529_ = lean_unsigned_to_nat(2u);
v_nbuckets_4530_ = lean_nat_mul(v___x_4528_, v___x_4529_);
v___x_4531_ = lean_unsigned_to_nat(0u);
v___x_4532_ = lean_box(0);
v___x_4533_ = lean_mk_array(v_nbuckets_4530_, v___x_4532_);
v___x_4534_ = lean_array_propagate_mark(v_data_4527_, v___x_4533_);
v___x_4535_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v___x_4531_, v_data_4527_, v___x_4534_);
return v___x_4535_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(uint8_t v_a_4536_, lean_object* v_x_4537_){
_start:
{
if (lean_obj_tag(v_x_4537_) == 0)
{
uint8_t v___x_4538_; 
v___x_4538_ = 0;
return v___x_4538_;
}
else
{
lean_object* v_key_4539_; lean_object* v_tail_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; uint8_t v___x_4544_; 
v_key_4539_ = lean_ctor_get(v_x_4537_, 0);
v_tail_4540_ = lean_ctor_get(v_x_4537_, 2);
v___x_4541_ = lean_obj_tag_nat(v_key_4539_);
v___x_4542_ = lean_box(v_a_4536_);
v___x_4543_ = lean_obj_tag_nat(v___x_4542_);
lean_dec(v___x_4542_);
v___x_4544_ = lean_nat_dec_eq(v___x_4541_, v___x_4543_);
if (v___x_4544_ == 0)
{
v_x_4537_ = v_tail_4540_;
goto _start;
}
else
{
return v___x_4544_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_4536_ = stack[0].m_num;
lean_object* v_x_4537_ = stack[1].m_obj;
uint8_t v_res_4546_;
v_res_4546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4536_, v_x_4537_);
stack->m_num = v_res_4546_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg___boxed(lean_object* v_a_4547_, lean_object* v_x_4548_){
_start:
{
uint8_t v_a_boxed_4549_; uint8_t v_res_4550_; lean_object* v_r_4551_; 
v_a_boxed_4549_ = lean_unbox(v_a_4547_);
v_res_4550_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_boxed_4549_, v_x_4548_);
lean_dec(v_x_4548_);
v_r_4551_ = lean_box(v_res_4550_);
return v_r_4551_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(lean_object* v_m_4552_, uint8_t v_a_4553_, lean_object* v_b_4554_){
_start:
{
lean_object* v_size_4555_; lean_object* v_buckets_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4600_; 
v_size_4555_ = lean_ctor_get(v_m_4552_, 0);
v_buckets_4556_ = lean_ctor_get(v_m_4552_, 1);
v_isSharedCheck_4600_ = !lean_is_exclusive(v_m_4552_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4558_ = v_m_4552_;
v_isShared_4559_ = v_isSharedCheck_4600_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_buckets_4556_);
lean_inc(v_size_4555_);
lean_dec(v_m_4552_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4600_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4560_; uint64_t v___x_4561_; uint64_t v___x_4562_; uint64_t v___x_4563_; uint64_t v_fold_4564_; uint64_t v___x_4565_; uint64_t v___x_4566_; uint64_t v___x_4567_; size_t v___x_4568_; size_t v___x_4569_; size_t v___x_4570_; size_t v___x_4571_; size_t v___x_4572_; lean_object* v_bkt_4573_; uint8_t v___x_4574_; 
v___x_4560_ = lean_array_get_size(v_buckets_4556_);
v___x_4561_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_4553_);
v___x_4562_ = 32ULL;
v___x_4563_ = lean_uint64_shift_right(v___x_4561_, v___x_4562_);
v_fold_4564_ = lean_uint64_xor(v___x_4561_, v___x_4563_);
v___x_4565_ = 16ULL;
v___x_4566_ = lean_uint64_shift_right(v_fold_4564_, v___x_4565_);
v___x_4567_ = lean_uint64_xor(v_fold_4564_, v___x_4566_);
v___x_4568_ = lean_uint64_to_usize(v___x_4567_);
v___x_4569_ = lean_usize_of_nat(v___x_4560_);
v___x_4570_ = ((size_t)1ULL);
v___x_4571_ = lean_usize_sub(v___x_4569_, v___x_4570_);
v___x_4572_ = lean_usize_land(v___x_4568_, v___x_4571_);
v_bkt_4573_ = lean_array_uget_borrowed(v_buckets_4556_, v___x_4572_);
v___x_4574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4553_, v_bkt_4573_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; lean_object* v_size_x27_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v_buckets_x27_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; uint8_t v___x_4585_; 
v___x_4575_ = lean_unsigned_to_nat(1u);
v_size_x27_4576_ = lean_nat_add(v_size_4555_, v___x_4575_);
lean_dec(v_size_4555_);
v___x_4577_ = lean_box(v_a_4553_);
lean_inc(v_bkt_4573_);
v___x_4578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v_b_4554_);
lean_ctor_set(v___x_4578_, 2, v_bkt_4573_);
v_buckets_x27_4579_ = lean_array_uset(v_buckets_4556_, v___x_4572_, v___x_4578_);
v___x_4580_ = lean_unsigned_to_nat(4u);
v___x_4581_ = lean_nat_mul(v_size_x27_4576_, v___x_4580_);
v___x_4582_ = lean_unsigned_to_nat(3u);
v___x_4583_ = lean_nat_div(v___x_4581_, v___x_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_array_get_size(v_buckets_x27_4579_);
v___x_4585_ = lean_nat_dec_le(v___x_4583_, v___x_4584_);
lean_dec(v___x_4583_);
if (v___x_4585_ == 0)
{
lean_object* v_val_4586_; lean_object* v___x_4588_; 
v_val_4586_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_buckets_x27_4579_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 1, v_val_4586_);
lean_ctor_set(v___x_4558_, 0, v_size_x27_4576_);
v___x_4588_ = v___x_4558_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_size_x27_4576_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_val_4586_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
else
{
lean_object* v___x_4591_; 
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 1, v_buckets_x27_4579_);
lean_ctor_set(v___x_4558_, 0, v_size_x27_4576_);
v___x_4591_ = v___x_4558_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_size_x27_4576_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_buckets_x27_4579_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
else
{
lean_object* v___x_4593_; lean_object* v_buckets_x27_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
lean_inc(v_bkt_4573_);
v___x_4593_ = lean_box(0);
v_buckets_x27_4594_ = lean_array_uset(v_buckets_4556_, v___x_4572_, v___x_4593_);
v___x_4595_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4553_, v_b_4554_, v_bkt_4573_);
v___x_4596_ = lean_array_uset(v_buckets_x27_4594_, v___x_4572_, v___x_4595_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 1, v___x_4596_);
v___x_4598_ = v___x_4558_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_size_4555_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4552_ = stack[0].m_obj;
uint8_t v_a_4553_ = stack[1].m_num;
lean_object* v_b_4554_ = stack[2].m_obj;
lean_object* v_res_4601_;
v_res_4601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4552_, v_a_4553_, v_b_4554_);
stack->m_obj
 = v_res_4601_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg___boxed(lean_object* v_m_4602_, lean_object* v_a_4603_, lean_object* v_b_4604_){
_start:
{
uint8_t v_a_boxed_4605_; lean_object* v_res_4606_; 
v_a_boxed_4605_ = lean_unbox(v_a_4603_);
v_res_4606_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4602_, v_a_boxed_4605_, v_b_4604_);
return v_res_4606_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(lean_object* v_cmd_4610_, lean_object* v_as_4611_, size_t v_sz_4612_, size_t v_i_4613_, lean_object* v_b_4614_){
_start:
{
lean_object* v_a_4617_; uint8_t v___x_4621_; 
v___x_4621_ = lean_usize_dec_lt(v_i_4613_, v_sz_4612_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v_b_4614_);
return v___x_4622_;
}
else
{
lean_object* v_a_4623_; lean_object* v_snd_4624_; lean_object* v_fst_4625_; lean_object* v_fst_4626_; lean_object* v_snd_4627_; lean_object* v_snd_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4726_; 
v_a_4623_ = lean_array_uget_borrowed(v_as_4611_, v_i_4613_);
v_snd_4624_ = lean_ctor_get(v_a_4623_, 1);
v_fst_4625_ = lean_ctor_get(v_a_4623_, 0);
v_fst_4626_ = lean_ctor_get(v_snd_4624_, 0);
v_snd_4627_ = lean_ctor_get(v_snd_4624_, 1);
lean_inc(v_snd_4627_);
v_snd_4628_ = lean_ctor_get(v_b_4614_, 1);
v_isSharedCheck_4726_ = !lean_is_exclusive(v_b_4614_);
if (v_isSharedCheck_4726_ == 0)
{
lean_object* v_unused_4727_; 
v_unused_4727_ = lean_ctor_get(v_b_4614_, 0);
lean_dec(v_unused_4727_);
v___x_4630_ = v_b_4614_;
v_isShared_4631_ = v_isSharedCheck_4726_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_snd_4628_);
lean_dec(v_b_4614_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4726_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4632_; 
v___x_4632_ = lean_box(0);
if (lean_obj_tag(v_snd_4627_) == 1)
{
lean_object* v_val_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4722_; 
v_val_4633_ = lean_ctor_get(v_snd_4627_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v_snd_4627_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4635_ = v_snd_4627_;
v_isShared_4636_ = v_isSharedCheck_4722_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_val_4633_);
lean_dec(v_snd_4627_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4722_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
uint8_t v___x_4637_; 
v___x_4637_ = l_System_FilePath_pathExists(v_val_4633_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4638_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4639_ = lean_string_append(v___x_4638_, v_cmd_4610_);
v___x_4640_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4641_ = lean_string_append(v___x_4639_, v___x_4640_);
v___x_4642_ = lean_string_append(v___x_4641_, v_fst_4625_);
v___x_4643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4644_ = lean_string_append(v___x_4642_, v___x_4643_);
v___x_4645_ = lean_string_append(v___x_4644_, v_val_4633_);
lean_dec(v_val_4633_);
v___x_4646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__1));
v___x_4647_ = lean_string_append(v___x_4645_, v___x_4646_);
v___x_4648_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4647_);
lean_dec_ref(v___x_4647_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4663_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4651_ = v___x_4648_;
v_isShared_4652_ = v_isSharedCheck_4663_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v___x_4648_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4663_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4653_, 0, v_a_4649_);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v___x_4653_);
v___x_4655_ = v___x_4635_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4653_);
v___x_4655_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4657_; 
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4655_);
v___x_4657_ = v___x_4630_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v_snd_4628_);
v___x_4657_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4659_; 
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4657_);
v___x_4659_ = v___x_4651_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4657_);
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
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_del_object(v___x_4635_);
lean_del_object(v___x_4630_);
lean_dec(v_snd_4628_);
v_a_4664_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4648_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4648_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
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
uint8_t v___x_4672_; 
v___x_4672_ = l_System_FilePath_isDir(v_val_4633_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; 
lean_del_object(v___x_4635_);
v___x_4673_ = lean_io_realpath(v_val_4633_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; uint8_t v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v___x_4675_ = lean_unbox(v_fst_4626_);
v___x_4676_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_snd_4628_, v___x_4675_, v_a_4674_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 1, v___x_4676_);
lean_ctor_set(v___x_4630_, 0, v___x_4632_);
v___x_4678_ = v___x_4630_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
v_a_4617_ = v___x_4678_;
goto v___jp_4616_;
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4687_; 
lean_del_object(v___x_4630_);
lean_dec(v_snd_4628_);
v_a_4680_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4682_ = v___x_4673_;
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4673_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
else
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4688_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4689_ = lean_string_append(v___x_4688_, v_cmd_4610_);
v___x_4690_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeLakeBuild___closed__0));
v___x_4691_ = lean_string_append(v___x_4689_, v___x_4690_);
v___x_4692_ = lean_string_append(v___x_4691_, v_fst_4625_);
v___x_4693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__0));
v___x_4694_ = lean_string_append(v___x_4692_, v___x_4693_);
v___x_4695_ = lean_string_append(v___x_4694_, v_val_4633_);
lean_dec(v_val_4633_);
v___x_4696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___closed__2));
v___x_4697_ = lean_string_append(v___x_4695_, v___x_4696_);
v___x_4698_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4697_);
lean_dec_ref(v___x_4697_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4713_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4713_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4713_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4703_; lean_object* v___x_4705_; 
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v_a_4699_);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v___x_4703_);
v___x_4705_ = v___x_4635_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4703_);
v___x_4705_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
lean_object* v___x_4707_; 
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4705_);
v___x_4707_ = v___x_4630_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4711_, 1, v_snd_4628_);
v___x_4707_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
lean_object* v___x_4709_; 
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 0, v___x_4707_);
v___x_4709_ = v___x_4701_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4707_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_del_object(v___x_4635_);
lean_del_object(v___x_4630_);
lean_dec(v_snd_4628_);
v_a_4714_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4698_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4698_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4724_; 
lean_dec(v_snd_4627_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4632_);
v___x_4724_ = v___x_4630_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4632_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_snd_4628_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
v_a_4617_ = v___x_4724_;
goto v___jp_4616_;
}
}
}
}
v___jp_4616_:
{
size_t v___x_4618_; size_t v___x_4619_; 
v___x_4618_ = ((size_t)1ULL);
v___x_4619_ = lean_usize_add(v_i_4613_, v___x_4618_);
v_i_4613_ = v___x_4619_;
v_b_4614_ = v_a_4617_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_4610_ = stack[0].m_obj;
lean_object* v_as_4611_ = stack[1].m_obj;
size_t v_sz_4612_ = stack[2].m_num;
size_t v_i_4613_ = stack[3].m_num;
lean_object* v_b_4614_ = stack[4].m_obj;
lean_object* v_res_4728_;
v_res_4728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4610_, v_as_4611_, v_sz_4612_, v_i_4613_, v_b_4614_);
stack->m_obj
 = v_res_4728_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1___boxed(lean_object* v_cmd_4729_, lean_object* v_as_4730_, lean_object* v_sz_4731_, lean_object* v_i_4732_, lean_object* v_b_4733_, lean_object* v___y_4734_){
_start:
{
size_t v_sz_boxed_4735_; size_t v_i_boxed_4736_; lean_object* v_res_4737_; 
v_sz_boxed_4735_ = lean_unbox_usize(v_sz_4731_);
lean_dec(v_sz_4731_);
v_i_boxed_4736_ = lean_unbox_usize(v_i_4732_);
lean_dec(v_i_4732_);
v_res_4737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4729_, v_as_4730_, v_sz_boxed_4735_, v_i_boxed_4736_, v_b_4733_);
lean_dec_ref(v_as_4730_);
lean_dec_ref(v_cmd_4729_);
return v_res_4737_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0(void){
_start:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4738_ = lean_box(0);
v___x_4739_ = lean_unsigned_to_nat(16u);
v___x_4740_ = lean_mk_array(v___x_4739_, v___x_4738_);
return v___x_4740_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1(void){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v_store_4743_; 
v___x_4741_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__0);
v___x_4742_ = lean_unsigned_to_nat(0u);
v_store_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_store_4743_, 0, v___x_4742_);
lean_ctor_set(v_store_4743_, 1, v___x_4741_);
return v_store_4743_;
}
}
static lean_object* _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2(void){
_start:
{
lean_object* v_store_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v_store_4744_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__1);
v___x_4745_ = lean_box(0);
v___x_4746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4745_);
lean_ctor_set(v___x_4746_, 1, v_store_4744_);
return v___x_4746_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(lean_object* v_cmd_4747_, lean_object* v_entries_4748_){
_start:
{
lean_object* v___x_4750_; size_t v_sz_4751_; size_t v___x_4752_; lean_object* v___x_4753_; 
v___x_4750_ = lean_obj_once(&l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2, &l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2_once, _init_l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___closed__2);
v_sz_4751_ = lean_array_size(v_entries_4748_);
v___x_4752_ = ((size_t)0ULL);
v___x_4753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__1(v_cmd_4747_, v_entries_4748_, v_sz_4751_, v___x_4752_, v___x_4750_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4768_; 
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4756_ = v___x_4753_;
v_isShared_4757_ = v_isSharedCheck_4768_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4753_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4768_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v_fst_4758_; 
v_fst_4758_ = lean_ctor_get(v_a_4754_, 0);
if (lean_obj_tag(v_fst_4758_) == 0)
{
lean_object* v_snd_4759_; lean_object* v___x_4760_; lean_object* v___x_4762_; 
v_snd_4759_ = lean_ctor_get(v_a_4754_, 1);
lean_inc(v_snd_4759_);
lean_dec(v_a_4754_);
v___x_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4760_, 0, v_snd_4759_);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v___x_4760_);
v___x_4762_ = v___x_4756_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4760_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
else
{
lean_object* v_val_4764_; lean_object* v___x_4766_; 
lean_inc_ref(v_fst_4758_);
lean_dec(v_a_4754_);
v_val_4764_ = lean_ctor_get(v_fst_4758_, 0);
lean_inc(v_val_4764_);
lean_dec_ref_known(v_fst_4758_, 1);
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v_val_4764_);
v___x_4766_ = v___x_4756_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_val_4764_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
v_a_4769_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___x_4753_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4753_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_4747_ = stack[0].m_obj;
lean_object* v_entries_4748_ = stack[1].m_obj;
lean_object* v_res_4777_;
v_res_4777_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v_cmd_4747_, v_entries_4748_);
stack->m_obj
 = v_res_4777_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore___boxed(lean_object* v_cmd_4778_, lean_object* v_entries_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v_cmd_4778_, v_entries_4779_);
lean_dec_ref(v_entries_4779_);
lean_dec_ref(v_cmd_4778_);
return v_res_4781_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(lean_object* v_00_u03b2_4782_, lean_object* v_m_4783_, uint8_t v_a_4784_, lean_object* v_b_4785_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___redArg(v_m_4783_, v_a_4784_, v_b_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_4783_ = stack[1].m_obj;
uint8_t v_a_4784_ = stack[2].m_num;
lean_object* v_b_4785_ = stack[3].m_obj;
lean_object* v_res_4787_;
v_res_4787_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(lean_box(0), v_m_4783_, v_a_4784_, v_b_4785_);
stack->m_obj
 = v_res_4787_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0___boxed(lean_object* v_00_u03b2_4788_, lean_object* v_m_4789_, lean_object* v_a_4790_, lean_object* v_b_4791_){
_start:
{
uint8_t v_a_boxed_4792_; lean_object* v_res_4793_; 
v_a_boxed_4792_ = lean_unbox(v_a_4790_);
v_res_4793_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0(v_00_u03b2_4788_, v_m_4789_, v_a_boxed_4792_, v_b_4791_);
return v_res_4793_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(lean_object* v_00_u03b2_4794_, uint8_t v_a_4795_, lean_object* v_x_4796_){
_start:
{
uint8_t v___x_4797_; 
v___x_4797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_4795_, v_x_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_4795_ = stack[1].m_num;
lean_object* v_x_4796_ = stack[2].m_obj;
uint8_t v_res_4798_;
v_res_4798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(lean_box(0), v_a_4795_, v_x_4796_);
stack->m_num = v_res_4798_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4799_, lean_object* v_a_4800_, lean_object* v_x_4801_){
_start:
{
uint8_t v_a_boxed_4802_; uint8_t v_res_4803_; lean_object* v_r_4804_; 
v_a_boxed_4802_ = lean_unbox(v_a_4800_);
v_res_4803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0(v_00_u03b2_4799_, v_a_boxed_4802_, v_x_4801_);
lean_dec(v_x_4801_);
v_r_4804_ = lean_box(v_res_4803_);
return v_r_4804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1(lean_object* v_00_u03b2_4805_, lean_object* v_data_4806_){
_start:
{
lean_object* v___x_4807_; 
v___x_4807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1___redArg(v_data_4806_);
return v___x_4807_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(lean_object* v_00_u03b2_4808_, uint8_t v_a_4809_, lean_object* v_b_4810_, lean_object* v_x_4811_){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___redArg(v_a_4809_, v_b_4810_, v_x_4811_);
return v___x_4812_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_4809_ = stack[1].m_num;
lean_object* v_b_4810_ = stack[2].m_obj;
lean_object* v_x_4811_ = stack[3].m_obj;
lean_object* v_res_4813_;
v_res_4813_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(lean_box(0), v_a_4809_, v_b_4810_, v_x_4811_);
stack->m_obj
 = v_res_4813_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4814_, lean_object* v_a_4815_, lean_object* v_b_4816_, lean_object* v_x_4817_){
_start:
{
uint8_t v_a_boxed_4818_; lean_object* v_res_4819_; 
v_a_boxed_4818_ = lean_unbox(v_a_4815_);
v_res_4819_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__2(v_00_u03b2_4814_, v_a_boxed_4818_, v_b_4816_, v_x_4817_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4820_, lean_object* v_i_4821_, lean_object* v_source_4822_, lean_object* v_target_4823_){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2___redArg(v_i_4821_, v_source_4822_, v_target_4823_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4825_, lean_object* v_x_4826_, lean_object* v_x_4827_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4826_, v_x_4827_);
return v___x_4828_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext(lean_object* v_cmd_4840_, uint8_t v_paranoid_4841_, uint8_t v_inadvisablyNoSandbox_4842_, lean_object* v_lean_4843_, lean_object* v_lake_4844_, lean_object* v_projectDir_4845_, lean_object* v_moduleStore_4846_){
_start:
{
lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v___y_4851_; lean_object* v___y_4852_; lean_object* v___y_4853_; lean_object* v___y_4854_; lean_object* v_whichSandbox_4881_; 
if (v_inadvisablyNoSandbox_4842_ == 0)
{
uint8_t v___x_4957_; 
v___x_4957_ = l_System_Platform_isLinux;
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
lean_dec_ref(v_moduleStore_4846_);
lean_dec_ref(v_projectDir_4845_);
lean_dec_ref(v_lean_4843_);
v___x_4958_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4959_ = lean_string_append(v___x_4958_, v_cmd_4840_);
v___x_4960_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__6));
v___x_4961_ = lean_string_append(v___x_4959_, v___x_4960_);
v___x_4962_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4961_);
lean_dec_ref(v___x_4961_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4971_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4965_ = v___x_4962_;
v_isShared_4966_ = v_isSharedCheck_4971_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v___x_4962_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4971_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4967_; lean_object* v___x_4969_; 
v___x_4967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4967_, 0, v_a_4963_);
if (v_isShared_4966_ == 0)
{
lean_ctor_set(v___x_4965_, 0, v___x_4967_);
v___x_4969_ = v___x_4965_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4967_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4979_; 
v_a_4972_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4979_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4979_ == 0)
{
v___x_4974_ = v___x_4962_;
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v___x_4962_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4979_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
v___x_4977_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
return v___x_4977_;
}
}
}
}
else
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___y_4983_; 
v___x_4980_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__7));
v___x_4981_ = lean_io_getenv(v___x_4980_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v___x_5019_; 
v___x_5019_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__8));
v___y_4983_ = v___x_5019_;
goto v___jp_4982_;
}
else
{
lean_object* v_val_5020_; 
v_val_5020_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_val_5020_);
lean_dec_ref_known(v___x_4981_, 1);
v___y_4983_ = v_val_5020_;
goto v___jp_4982_;
}
v___jp_4982_:
{
lean_object* v___x_4984_; lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_5018_; 
lean_inc_ref(v___y_4983_);
v___x_4984_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___y_4983_);
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_4984_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_4987_ = v___x_4984_;
v_isShared_4988_ = v_isSharedCheck_5018_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4984_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_5018_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
if (lean_obj_tag(v_a_4985_) == 1)
{
lean_object* v_val_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_del_object(v___x_4987_);
lean_dec_ref(v___y_4983_);
v_val_4989_ = lean_ctor_get(v_a_4985_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v_a_4985_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v_a_4985_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_val_4989_);
lean_dec(v_a_4985_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_val_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
v_whichSandbox_4881_ = v___x_4994_;
goto v___jp_4880_;
}
}
}
else
{
lean_object* v___x_4997_; lean_object* v___x_4998_; 
lean_dec(v_a_4985_);
lean_dec_ref(v_moduleStore_4846_);
lean_dec_ref(v_projectDir_4845_);
lean_dec_ref(v_lean_4843_);
v___x_4997_ = l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError(v_cmd_4840_, v___y_4983_);
lean_dec_ref(v___y_4983_);
v___x_4998_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4997_);
lean_dec_ref(v___x_4997_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5009_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5001_ = v___x_4998_;
v_isShared_5002_ = v_isSharedCheck_5009_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4998_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5009_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_4988_ == 0)
{
lean_ctor_set(v___x_4987_, 0, v_a_4999_);
v___x_5004_ = v___x_4987_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
lean_object* v___x_5006_; 
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 0, v___x_5004_);
v___x_5006_ = v___x_5001_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
lean_del_object(v___x_4987_);
v_a_5010_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_4998_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_4998_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
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
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__9));
v___x_5022_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5021_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v___x_5023_; 
lean_dec_ref_known(v___x_5022_, 1);
v___x_5023_ = lean_box(0);
v_whichSandbox_4881_ = v___x_5023_;
goto v___jp_4880_;
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec_ref(v_moduleStore_4846_);
lean_dec_ref(v_projectDir_4845_);
lean_dec_ref(v_lean_4843_);
v_a_5024_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_5022_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5022_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
v___jp_4848_:
{
lean_object* v___x_4855_; 
v___x_4855_ = lean_io_realpath(v_projectDir_4845_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4871_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4858_ = v___x_4855_;
v_isShared_4859_ = v_isSharedCheck_4871_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4855_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4871_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v_home_4860_; lean_object* v_lake_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4869_; 
v_home_4860_ = lean_ctor_get(v_lake_4844_, 0);
v_lake_4861_ = lean_ctor_get(v_lake_4844_, 5);
v___x_4862_ = lean_box(0);
v___x_4863_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_builtinTargets___closed__0));
v___x_4864_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_4865_ = lean_box(1);
lean_inc_ref(v_home_4860_);
lean_inc_ref(v_lake_4861_);
v___x_4866_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_4866_, 0, v_a_4856_);
lean_ctor_set(v___x_4866_, 1, v___x_4862_);
lean_ctor_set(v___x_4866_, 2, v___x_4862_);
lean_ctor_set(v___x_4866_, 3, v___x_4863_);
lean_ctor_set(v___x_4866_, 4, v___x_4863_);
lean_ctor_set(v___x_4866_, 5, v___x_4863_);
lean_ctor_set(v___x_4866_, 6, v___y_4849_);
lean_ctor_set(v___x_4866_, 7, v___x_4864_);
lean_ctor_set(v___x_4866_, 8, v___x_4864_);
lean_ctor_set(v___x_4866_, 9, v___y_4853_);
lean_ctor_set(v___x_4866_, 10, v_lake_4861_);
lean_ctor_set(v___x_4866_, 11, v_home_4860_);
lean_ctor_set(v___x_4866_, 12, v___y_4852_);
lean_ctor_set(v___x_4866_, 13, v___y_4850_);
lean_ctor_set(v___x_4866_, 14, v___y_4851_);
lean_ctor_set(v___x_4866_, 15, v___x_4865_);
lean_ctor_set(v___x_4866_, 16, v___y_4854_);
lean_ctor_set(v___x_4866_, 17, v_moduleStore_4846_);
v___x_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4866_);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 0, v___x_4867_);
v___x_4869_ = v___x_4858_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4867_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_dec_ref(v___y_4854_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec_ref(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec_ref(v_moduleStore_4846_);
v_a_4872_ = lean_ctor_get(v___x_4855_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4855_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4855_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
v___jp_4880_:
{
lean_object* v_sysroot_4882_; lean_object* v_binDir_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v_whichLean4Export_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v_whichLeanChecker_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4956_; 
v_sysroot_4882_ = lean_ctor_get(v_lean_4843_, 0);
lean_inc_ref(v_sysroot_4882_);
v_binDir_4883_ = lean_ctor_get(v_lean_4843_, 6);
v___x_4884_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__0));
lean_inc_ref_n(v_binDir_4883_, 2);
v___x_4885_ = l_System_FilePath_join(v_binDir_4883_, v___x_4884_);
v___x_4886_ = l_System_FilePath_exeExtension;
v_whichLean4Export_4887_ = l_System_FilePath_addExtension(v___x_4885_, v___x_4886_);
v___x_4888_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__1));
v___x_4889_ = l_System_FilePath_join(v_binDir_4883_, v___x_4888_);
v_whichLeanChecker_4890_ = l_System_FilePath_addExtension(v___x_4889_, v___x_4886_);
v___x_4891_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__2));
v___x_4892_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4891_);
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4895_ = v___x_4892_;
v_isShared_4896_ = v_isSharedCheck_4956_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4892_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4956_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
if (lean_obj_tag(v_a_4893_) == 1)
{
lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4931_; 
lean_dec_ref_known(v_a_4893_, 1);
lean_del_object(v___x_4895_);
v___x_4897_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__4));
v___x_4898_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_4897_);
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4901_ = v___x_4898_;
v_isShared_4902_ = v_isSharedCheck_4931_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4898_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4931_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
if (lean_obj_tag(v_a_4899_) == 1)
{
lean_del_object(v___x_4901_);
if (v_paranoid_4841_ == 0)
{
lean_object* v_val_4903_; lean_object* v___x_4904_; 
lean_dec_ref(v_lean_4843_);
v_val_4903_ = lean_ctor_get(v_a_4899_, 0);
lean_inc(v_val_4903_);
lean_dec_ref_known(v_a_4899_, 1);
v___x_4904_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__3));
v___y_4849_ = v_sysroot_4882_;
v___y_4850_ = v_whichLeanChecker_4890_;
v___y_4851_ = v_val_4903_;
v___y_4852_ = v_whichLean4Export_4887_;
v___y_4853_ = v_whichSandbox_4881_;
v___y_4854_ = v___x_4904_;
goto v___jp_4848_;
}
else
{
lean_object* v_val_4905_; lean_object* v___x_4906_; 
v_val_4905_ = lean_ctor_get(v_a_4899_, 0);
lean_inc(v_val_4905_);
lean_dec_ref_known(v_a_4899_, 1);
v___x_4906_ = l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels(v_lean_4843_);
v___y_4849_ = v_sysroot_4882_;
v___y_4850_ = v_whichLeanChecker_4890_;
v___y_4851_ = v_val_4905_;
v___y_4852_ = v_whichLean4Export_4887_;
v___y_4853_ = v_whichSandbox_4881_;
v___y_4854_ = v___x_4906_;
goto v___jp_4848_;
}
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_dec(v_a_4899_);
lean_dec_ref(v_whichLeanChecker_4890_);
lean_dec_ref(v_whichLean4Export_4887_);
lean_dec_ref(v_sysroot_4882_);
lean_dec(v_whichSandbox_4881_);
lean_dec_ref(v_moduleStore_4846_);
lean_dec_ref(v_projectDir_4845_);
lean_dec_ref(v_lean_4843_);
v___x_4907_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4908_ = lean_string_append(v___x_4907_, v_cmd_4840_);
v___x_4909_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__4));
v___x_4910_ = lean_string_append(v___x_4908_, v___x_4909_);
v___x_4911_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4910_);
lean_dec_ref(v___x_4910_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4922_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4922_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4922_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set(v___x_4901_, 0, v_a_4912_);
v___x_4917_ = v___x_4901_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
lean_object* v___x_4919_; 
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v___x_4917_);
v___x_4919_ = v___x_4914_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4917_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_del_object(v___x_4901_);
v_a_4923_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4911_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4911_);
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
}
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
lean_dec(v_a_4893_);
lean_dec_ref(v_whichLeanChecker_4890_);
lean_dec_ref(v_whichLean4Export_4887_);
lean_dec_ref(v_sysroot_4882_);
lean_dec(v_whichSandbox_4881_);
lean_dec_ref(v_moduleStore_4846_);
lean_dec_ref(v_projectDir_4845_);
lean_dec_ref(v_lean_4843_);
v___x_4932_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_missingSandboxError___closed__0));
v___x_4933_ = lean_string_append(v___x_4932_, v_cmd_4840_);
v___x_4934_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_mkContext___closed__5));
v___x_4935_ = lean_string_append(v___x_4933_, v___x_4934_);
v___x_4936_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_4935_);
lean_dec_ref(v___x_4935_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4947_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4939_ = v___x_4936_;
v_isShared_4940_ = v_isSharedCheck_4947_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4947_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4896_ == 0)
{
lean_ctor_set(v___x_4895_, 0, v_a_4937_);
v___x_4942_ = v___x_4895_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4944_; 
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4942_);
v___x_4944_ = v___x_4939_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v___x_4942_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_del_object(v___x_4895_);
v_a_4948_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4936_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4936_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_mkContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_4840_ = stack[0].m_obj;
uint8_t v_paranoid_4841_ = stack[1].m_num;
uint8_t v_inadvisablyNoSandbox_4842_ = stack[2].m_num;
lean_object* v_lean_4843_ = stack[3].m_obj;
lean_object* v_lake_4844_ = stack[4].m_obj;
lean_object* v_projectDir_4845_ = stack[5].m_obj;
lean_object* v_moduleStore_4846_ = stack[6].m_obj;
lean_object* v_res_5032_;
v_res_5032_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_4840_, v_paranoid_4841_, v_inadvisablyNoSandbox_4842_, v_lean_4843_, v_lake_4844_, v_projectDir_4845_, v_moduleStore_4846_);
stack->m_obj
 = v_res_5032_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_mkContext___boxed(lean_object* v_cmd_5033_, lean_object* v_paranoid_5034_, lean_object* v_inadvisablyNoSandbox_5035_, lean_object* v_lean_5036_, lean_object* v_lake_5037_, lean_object* v_projectDir_5038_, lean_object* v_moduleStore_5039_, lean_object* v_a_5040_){
_start:
{
uint8_t v_paranoid_boxed_5041_; uint8_t v_inadvisablyNoSandbox_boxed_5042_; lean_object* v_res_5043_; 
v_paranoid_boxed_5041_ = lean_unbox(v_paranoid_5034_);
v_inadvisablyNoSandbox_boxed_5042_ = lean_unbox(v_inadvisablyNoSandbox_5035_);
v_res_5043_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v_cmd_5033_, v_paranoid_boxed_5041_, v_inadvisablyNoSandbox_boxed_5042_, v_lean_5036_, v_lake_5037_, v_projectDir_5038_, v_moduleStore_5039_);
lean_dec_ref(v_lake_5037_);
lean_dec_ref(v_cmd_5033_);
return v_res_5043_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(lean_object* v_init_5050_, lean_object* v_x_5051_){
_start:
{
lean_object* v_d_5054_; 
if (lean_obj_tag(v_x_5051_) == 0)
{
lean_object* v_k_5057_; lean_object* v_v_5058_; lean_object* v_l_5059_; lean_object* v_r_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v_k_5057_ = lean_ctor_get(v_x_5051_, 1);
v_v_5058_ = lean_ctor_get(v_x_5051_, 2);
v_l_5059_ = lean_ctor_get(v_x_5051_, 3);
v_r_5060_ = lean_ctor_get(v_x_5051_, 4);
v___x_5061_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__14));
v___x_5062_ = lean_box(0);
v___x_5063_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5064_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_5050_, v_l_5059_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_a_5065_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref_known(v___x_5064_, 1);
if (lean_obj_tag(v_a_5065_) == 0)
{
lean_object* v_a_5066_; 
v_a_5066_ = lean_ctor_get(v_a_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v_a_5065_, 1);
v_d_5054_ = v_a_5066_;
goto v___jp_5053_;
}
else
{
lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5103_; 
v_isSharedCheck_5103_ = !lean_is_exclusive(v_a_5065_);
if (v_isSharedCheck_5103_ == 0)
{
lean_object* v_unused_5104_; 
v_unused_5104_ = lean_ctor_get(v_a_5065_, 0);
lean_dec(v_unused_5104_);
v___x_5068_ = v_a_5065_;
v_isShared_5069_ = v_isSharedCheck_5103_;
goto v_resetjp_5067_;
}
else
{
lean_dec(v_a_5065_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5103_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5102_; 
v___x_5070_ = lean_unsigned_to_nat(0u);
v___x_5071_ = lean_array_get_borrowed(v___x_5061_, v_v_5058_, v___x_5070_);
lean_inc(v___x_5071_);
v___x_5072_ = l___private_Lake_CLI_Check_0__Lake_Check_whichExe(v___x_5071_);
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5075_ = v___x_5072_;
v_isShared_5076_ = v_isSharedCheck_5102_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5072_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5102_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
if (lean_obj_tag(v_a_5073_) == 0)
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5077_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_5078_ = lean_string_append(v___x_5077_, v_k_5057_);
v___x_5079_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__2));
v___x_5080_ = lean_string_append(v___x_5078_, v___x_5079_);
v___x_5081_ = lean_string_append(v___x_5080_, v___x_5071_);
v___x_5082_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__3));
v___x_5083_ = lean_string_append(v___x_5081_, v___x_5082_);
v___x_5084_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5083_);
lean_dec_ref(v___x_5083_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5087_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5084_, 1);
if (v_isShared_5076_ == 0)
{
lean_ctor_set(v___x_5075_, 0, v_a_5085_);
v___x_5087_ = v___x_5075_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5085_);
v___x_5087_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
lean_object* v___x_5089_; 
if (v_isShared_5069_ == 0)
{
lean_ctor_set(v___x_5068_, 0, v___x_5087_);
v___x_5089_ = v___x_5068_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v___x_5087_);
v___x_5089_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
lean_object* v___x_5090_; 
v___x_5090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5089_);
lean_ctor_set(v___x_5090_, 1, v___x_5062_);
v_d_5054_ = v___x_5090_;
goto v___jp_5053_;
}
}
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_del_object(v___x_5075_);
lean_del_object(v___x_5068_);
v_a_5093_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5084_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5084_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_5073_, 1);
lean_del_object(v___x_5075_);
lean_del_object(v___x_5068_);
v_init_5050_ = v___x_5063_;
v_x_5051_ = v_r_5060_;
goto _start;
}
}
}
}
}
else
{
return v___x_5064_;
}
}
else
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5105_, 0, v_init_5050_);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
return v___x_5106_;
}
v___jp_5053_:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5055_, 0, v_d_5054_);
v___x_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
return v___x_5056_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_5050_ = stack[0].m_obj;
lean_object* v_x_5051_ = stack[1].m_obj;
lean_object* v_res_5107_;
v_res_5107_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_5050_, v_x_5051_);
stack->m_obj
 = v_res_5107_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___boxed(lean_object* v_init_5108_, lean_object* v_x_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v_init_5108_, v_x_5109_);
lean_dec(v_x_5109_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(lean_object* v_k_5112_, lean_object* v_v_5113_, lean_object* v_t_5114_){
_start:
{
if (lean_obj_tag(v_t_5114_) == 0)
{
lean_object* v_size_5115_; lean_object* v_k_5116_; lean_object* v_v_5117_; lean_object* v_l_5118_; lean_object* v_r_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5399_; 
v_size_5115_ = lean_ctor_get(v_t_5114_, 0);
v_k_5116_ = lean_ctor_get(v_t_5114_, 1);
v_v_5117_ = lean_ctor_get(v_t_5114_, 2);
v_l_5118_ = lean_ctor_get(v_t_5114_, 3);
v_r_5119_ = lean_ctor_get(v_t_5114_, 4);
v_isSharedCheck_5399_ = !lean_is_exclusive(v_t_5114_);
if (v_isSharedCheck_5399_ == 0)
{
v___x_5121_ = v_t_5114_;
v_isShared_5122_ = v_isSharedCheck_5399_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_r_5119_);
lean_inc(v_l_5118_);
lean_inc(v_v_5117_);
lean_inc(v_k_5116_);
lean_inc(v_size_5115_);
lean_dec(v_t_5114_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5399_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
uint8_t v___x_5123_; 
v___x_5123_ = lean_string_compare(v_k_5112_, v_k_5116_);
switch(v___x_5123_)
{
case 0:
{
lean_object* v_impl_5124_; lean_object* v___x_5125_; 
lean_dec(v_size_5115_);
v_impl_5124_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5112_, v_v_5113_, v_l_5118_);
v___x_5125_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5119_) == 0)
{
lean_object* v_size_5126_; lean_object* v_size_5127_; lean_object* v_k_5128_; lean_object* v_v_5129_; lean_object* v_l_5130_; lean_object* v_r_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; uint8_t v___x_5134_; 
v_size_5126_ = lean_ctor_get(v_r_5119_, 0);
v_size_5127_ = lean_ctor_get(v_impl_5124_, 0);
v_k_5128_ = lean_ctor_get(v_impl_5124_, 1);
v_v_5129_ = lean_ctor_get(v_impl_5124_, 2);
v_l_5130_ = lean_ctor_get(v_impl_5124_, 3);
v_r_5131_ = lean_ctor_get(v_impl_5124_, 4);
lean_inc(v_r_5131_);
v___x_5132_ = lean_unsigned_to_nat(3u);
v___x_5133_ = lean_nat_mul(v___x_5132_, v_size_5126_);
v___x_5134_ = lean_nat_dec_lt(v___x_5133_, v_size_5127_);
lean_dec(v___x_5133_);
if (v___x_5134_ == 0)
{
lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5138_; 
lean_dec(v_r_5131_);
v___x_5135_ = lean_nat_add(v___x_5125_, v_size_5127_);
v___x_5136_ = lean_nat_add(v___x_5135_, v_size_5126_);
lean_dec(v___x_5135_);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 3, v_impl_5124_);
lean_ctor_set(v___x_5121_, 0, v___x_5136_);
v___x_5138_ = v___x_5121_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5139_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5139_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5139_, 3, v_impl_5124_);
lean_ctor_set(v_reuseFailAlloc_5139_, 4, v_r_5119_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
else
{
lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5205_; 
lean_inc(v_l_5130_);
lean_inc(v_v_5129_);
lean_inc(v_k_5128_);
lean_inc(v_size_5127_);
v_isSharedCheck_5205_ = !lean_is_exclusive(v_impl_5124_);
if (v_isSharedCheck_5205_ == 0)
{
lean_object* v_unused_5206_; lean_object* v_unused_5207_; lean_object* v_unused_5208_; lean_object* v_unused_5209_; lean_object* v_unused_5210_; 
v_unused_5206_ = lean_ctor_get(v_impl_5124_, 4);
lean_dec(v_unused_5206_);
v_unused_5207_ = lean_ctor_get(v_impl_5124_, 3);
lean_dec(v_unused_5207_);
v_unused_5208_ = lean_ctor_get(v_impl_5124_, 2);
lean_dec(v_unused_5208_);
v_unused_5209_ = lean_ctor_get(v_impl_5124_, 1);
lean_dec(v_unused_5209_);
v_unused_5210_ = lean_ctor_get(v_impl_5124_, 0);
lean_dec(v_unused_5210_);
v___x_5141_ = v_impl_5124_;
v_isShared_5142_ = v_isSharedCheck_5205_;
goto v_resetjp_5140_;
}
else
{
lean_dec(v_impl_5124_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5205_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v_size_5143_; lean_object* v_size_5144_; lean_object* v_k_5145_; lean_object* v_v_5146_; lean_object* v_l_5147_; lean_object* v_r_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; 
v_size_5143_ = lean_ctor_get(v_l_5130_, 0);
v_size_5144_ = lean_ctor_get(v_r_5131_, 0);
v_k_5145_ = lean_ctor_get(v_r_5131_, 1);
v_v_5146_ = lean_ctor_get(v_r_5131_, 2);
v_l_5147_ = lean_ctor_get(v_r_5131_, 3);
v_r_5148_ = lean_ctor_get(v_r_5131_, 4);
v___x_5149_ = lean_unsigned_to_nat(2u);
v___x_5150_ = lean_nat_mul(v___x_5149_, v_size_5143_);
v___x_5151_ = lean_nat_dec_lt(v_size_5144_, v___x_5150_);
lean_dec(v___x_5150_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5180_; 
lean_inc(v_r_5148_);
lean_inc(v_l_5147_);
lean_inc(v_v_5146_);
lean_inc(v_k_5145_);
v_isSharedCheck_5180_ = !lean_is_exclusive(v_r_5131_);
if (v_isSharedCheck_5180_ == 0)
{
lean_object* v_unused_5181_; lean_object* v_unused_5182_; lean_object* v_unused_5183_; lean_object* v_unused_5184_; lean_object* v_unused_5185_; 
v_unused_5181_ = lean_ctor_get(v_r_5131_, 4);
lean_dec(v_unused_5181_);
v_unused_5182_ = lean_ctor_get(v_r_5131_, 3);
lean_dec(v_unused_5182_);
v_unused_5183_ = lean_ctor_get(v_r_5131_, 2);
lean_dec(v_unused_5183_);
v_unused_5184_ = lean_ctor_get(v_r_5131_, 1);
lean_dec(v_unused_5184_);
v_unused_5185_ = lean_ctor_get(v_r_5131_, 0);
lean_dec(v_unused_5185_);
v___x_5153_ = v_r_5131_;
v_isShared_5154_ = v_isSharedCheck_5180_;
goto v_resetjp_5152_;
}
else
{
lean_dec(v_r_5131_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5180_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___y_5158_; lean_object* v___y_5159_; lean_object* v___y_5160_; lean_object* v___x_5168_; lean_object* v___y_5170_; 
v___x_5155_ = lean_nat_add(v___x_5125_, v_size_5127_);
lean_dec(v_size_5127_);
v___x_5156_ = lean_nat_add(v___x_5155_, v_size_5126_);
lean_dec(v___x_5155_);
v___x_5168_ = lean_nat_add(v___x_5125_, v_size_5143_);
if (lean_obj_tag(v_l_5147_) == 0)
{
lean_object* v_size_5178_; 
v_size_5178_ = lean_ctor_get(v_l_5147_, 0);
lean_inc(v_size_5178_);
v___y_5170_ = v_size_5178_;
goto v___jp_5169_;
}
else
{
lean_object* v___x_5179_; 
v___x_5179_ = lean_unsigned_to_nat(0u);
v___y_5170_ = v___x_5179_;
goto v___jp_5169_;
}
v___jp_5157_:
{
lean_object* v___x_5161_; lean_object* v___x_5163_; 
v___x_5161_ = lean_nat_add(v___y_5159_, v___y_5160_);
lean_dec(v___y_5160_);
lean_dec(v___y_5159_);
if (v_isShared_5154_ == 0)
{
lean_ctor_set(v___x_5153_, 4, v_r_5119_);
lean_ctor_set(v___x_5153_, 3, v_r_5148_);
lean_ctor_set(v___x_5153_, 2, v_v_5117_);
lean_ctor_set(v___x_5153_, 1, v_k_5116_);
lean_ctor_set(v___x_5153_, 0, v___x_5161_);
v___x_5163_ = v___x_5153_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5161_);
lean_ctor_set(v_reuseFailAlloc_5167_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5167_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5167_, 3, v_r_5148_);
lean_ctor_set(v_reuseFailAlloc_5167_, 4, v_r_5119_);
v___x_5163_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
lean_object* v___x_5165_; 
if (v_isShared_5142_ == 0)
{
lean_ctor_set(v___x_5141_, 4, v___x_5163_);
lean_ctor_set(v___x_5141_, 3, v___y_5158_);
lean_ctor_set(v___x_5141_, 2, v_v_5146_);
lean_ctor_set(v___x_5141_, 1, v_k_5145_);
lean_ctor_set(v___x_5141_, 0, v___x_5156_);
v___x_5165_ = v___x_5141_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5156_);
lean_ctor_set(v_reuseFailAlloc_5166_, 1, v_k_5145_);
lean_ctor_set(v_reuseFailAlloc_5166_, 2, v_v_5146_);
lean_ctor_set(v_reuseFailAlloc_5166_, 3, v___y_5158_);
lean_ctor_set(v_reuseFailAlloc_5166_, 4, v___x_5163_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
return v___x_5165_;
}
}
}
v___jp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_5173_; 
v___x_5171_ = lean_nat_add(v___x_5168_, v___y_5170_);
lean_dec(v___y_5170_);
lean_dec(v___x_5168_);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v_l_5147_);
lean_ctor_set(v___x_5121_, 3, v_l_5130_);
lean_ctor_set(v___x_5121_, 2, v_v_5129_);
lean_ctor_set(v___x_5121_, 1, v_k_5128_);
lean_ctor_set(v___x_5121_, 0, v___x_5171_);
v___x_5173_ = v___x_5121_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5171_);
lean_ctor_set(v_reuseFailAlloc_5177_, 1, v_k_5128_);
lean_ctor_set(v_reuseFailAlloc_5177_, 2, v_v_5129_);
lean_ctor_set(v_reuseFailAlloc_5177_, 3, v_l_5130_);
lean_ctor_set(v_reuseFailAlloc_5177_, 4, v_l_5147_);
v___x_5173_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
lean_object* v___x_5174_; 
v___x_5174_ = lean_nat_add(v___x_5125_, v_size_5126_);
if (lean_obj_tag(v_r_5148_) == 0)
{
lean_object* v_size_5175_; 
v_size_5175_ = lean_ctor_get(v_r_5148_, 0);
lean_inc(v_size_5175_);
v___y_5158_ = v___x_5173_;
v___y_5159_ = v___x_5174_;
v___y_5160_ = v_size_5175_;
goto v___jp_5157_;
}
else
{
lean_object* v___x_5176_; 
v___x_5176_ = lean_unsigned_to_nat(0u);
v___y_5158_ = v___x_5173_;
v___y_5159_ = v___x_5174_;
v___y_5160_ = v___x_5176_;
goto v___jp_5157_;
}
}
}
}
}
else
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5191_; 
lean_del_object(v___x_5121_);
v___x_5186_ = lean_nat_add(v___x_5125_, v_size_5127_);
lean_dec(v_size_5127_);
v___x_5187_ = lean_nat_add(v___x_5186_, v_size_5126_);
lean_dec(v___x_5186_);
v___x_5188_ = lean_nat_add(v___x_5125_, v_size_5126_);
v___x_5189_ = lean_nat_add(v___x_5188_, v_size_5144_);
lean_dec(v___x_5188_);
lean_inc_ref(v_r_5119_);
if (v_isShared_5142_ == 0)
{
lean_ctor_set(v___x_5141_, 4, v_r_5119_);
lean_ctor_set(v___x_5141_, 3, v_r_5131_);
lean_ctor_set(v___x_5141_, 2, v_v_5117_);
lean_ctor_set(v___x_5141_, 1, v_k_5116_);
lean_ctor_set(v___x_5141_, 0, v___x_5189_);
v___x_5191_ = v___x_5141_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v___x_5189_);
lean_ctor_set(v_reuseFailAlloc_5204_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5204_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5204_, 3, v_r_5131_);
lean_ctor_set(v_reuseFailAlloc_5204_, 4, v_r_5119_);
v___x_5191_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
v_isSharedCheck_5198_ = !lean_is_exclusive(v_r_5119_);
if (v_isSharedCheck_5198_ == 0)
{
lean_object* v_unused_5199_; lean_object* v_unused_5200_; lean_object* v_unused_5201_; lean_object* v_unused_5202_; lean_object* v_unused_5203_; 
v_unused_5199_ = lean_ctor_get(v_r_5119_, 4);
lean_dec(v_unused_5199_);
v_unused_5200_ = lean_ctor_get(v_r_5119_, 3);
lean_dec(v_unused_5200_);
v_unused_5201_ = lean_ctor_get(v_r_5119_, 2);
lean_dec(v_unused_5201_);
v_unused_5202_ = lean_ctor_get(v_r_5119_, 1);
lean_dec(v_unused_5202_);
v_unused_5203_ = lean_ctor_get(v_r_5119_, 0);
lean_dec(v_unused_5203_);
v___x_5193_ = v_r_5119_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_dec(v_r_5119_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 4, v___x_5191_);
lean_ctor_set(v___x_5193_, 3, v_l_5130_);
lean_ctor_set(v___x_5193_, 2, v_v_5129_);
lean_ctor_set(v___x_5193_, 1, v_k_5128_);
lean_ctor_set(v___x_5193_, 0, v___x_5187_);
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v___x_5187_);
lean_ctor_set(v_reuseFailAlloc_5197_, 1, v_k_5128_);
lean_ctor_set(v_reuseFailAlloc_5197_, 2, v_v_5129_);
lean_ctor_set(v_reuseFailAlloc_5197_, 3, v_l_5130_);
lean_ctor_set(v_reuseFailAlloc_5197_, 4, v___x_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5211_; 
v_l_5211_ = lean_ctor_get(v_impl_5124_, 3);
if (lean_obj_tag(v_l_5211_) == 0)
{
lean_object* v_r_5212_; lean_object* v_k_5213_; lean_object* v_v_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5225_; 
lean_inc_ref(v_l_5211_);
v_r_5212_ = lean_ctor_get(v_impl_5124_, 4);
v_k_5213_ = lean_ctor_get(v_impl_5124_, 1);
v_v_5214_ = lean_ctor_get(v_impl_5124_, 2);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_impl_5124_);
if (v_isSharedCheck_5225_ == 0)
{
lean_object* v_unused_5226_; lean_object* v_unused_5227_; 
v_unused_5226_ = lean_ctor_get(v_impl_5124_, 3);
lean_dec(v_unused_5226_);
v_unused_5227_ = lean_ctor_get(v_impl_5124_, 0);
lean_dec(v_unused_5227_);
v___x_5216_ = v_impl_5124_;
v_isShared_5217_ = v_isSharedCheck_5225_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_r_5212_);
lean_inc(v_v_5214_);
lean_inc(v_k_5213_);
lean_dec(v_impl_5124_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5225_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5218_; lean_object* v___x_5220_; 
v___x_5218_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5212_);
if (v_isShared_5217_ == 0)
{
lean_ctor_set(v___x_5216_, 3, v_r_5212_);
lean_ctor_set(v___x_5216_, 2, v_v_5117_);
lean_ctor_set(v___x_5216_, 1, v_k_5116_);
lean_ctor_set(v___x_5216_, 0, v___x_5125_);
v___x_5220_ = v___x_5216_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5125_);
lean_ctor_set(v_reuseFailAlloc_5224_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5224_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5224_, 3, v_r_5212_);
lean_ctor_set(v_reuseFailAlloc_5224_, 4, v_r_5212_);
v___x_5220_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5222_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v___x_5220_);
lean_ctor_set(v___x_5121_, 3, v_l_5211_);
lean_ctor_set(v___x_5121_, 2, v_v_5214_);
lean_ctor_set(v___x_5121_, 1, v_k_5213_);
lean_ctor_set(v___x_5121_, 0, v___x_5218_);
v___x_5222_ = v___x_5121_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5218_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_k_5213_);
lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_v_5214_);
lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_l_5211_);
lean_ctor_set(v_reuseFailAlloc_5223_, 4, v___x_5220_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
else
{
lean_object* v_r_5228_; 
v_r_5228_ = lean_ctor_get(v_impl_5124_, 4);
lean_inc(v_r_5228_);
if (lean_obj_tag(v_r_5228_) == 0)
{
lean_object* v_k_5229_; lean_object* v_v_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5253_; 
lean_inc(v_l_5211_);
v_k_5229_ = lean_ctor_get(v_impl_5124_, 1);
v_v_5230_ = lean_ctor_get(v_impl_5124_, 2);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_impl_5124_);
if (v_isSharedCheck_5253_ == 0)
{
lean_object* v_unused_5254_; lean_object* v_unused_5255_; lean_object* v_unused_5256_; 
v_unused_5254_ = lean_ctor_get(v_impl_5124_, 4);
lean_dec(v_unused_5254_);
v_unused_5255_ = lean_ctor_get(v_impl_5124_, 3);
lean_dec(v_unused_5255_);
v_unused_5256_ = lean_ctor_get(v_impl_5124_, 0);
lean_dec(v_unused_5256_);
v___x_5232_ = v_impl_5124_;
v_isShared_5233_ = v_isSharedCheck_5253_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_v_5230_);
lean_inc(v_k_5229_);
lean_dec(v_impl_5124_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5253_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v_k_5234_; lean_object* v_v_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5249_; 
v_k_5234_ = lean_ctor_get(v_r_5228_, 1);
v_v_5235_ = lean_ctor_get(v_r_5228_, 2);
v_isSharedCheck_5249_ = !lean_is_exclusive(v_r_5228_);
if (v_isSharedCheck_5249_ == 0)
{
lean_object* v_unused_5250_; lean_object* v_unused_5251_; lean_object* v_unused_5252_; 
v_unused_5250_ = lean_ctor_get(v_r_5228_, 4);
lean_dec(v_unused_5250_);
v_unused_5251_ = lean_ctor_get(v_r_5228_, 3);
lean_dec(v_unused_5251_);
v_unused_5252_ = lean_ctor_get(v_r_5228_, 0);
lean_dec(v_unused_5252_);
v___x_5237_ = v_r_5228_;
v_isShared_5238_ = v_isSharedCheck_5249_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_v_5235_);
lean_inc(v_k_5234_);
lean_dec(v_r_5228_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5249_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5239_; lean_object* v___x_5241_; 
v___x_5239_ = lean_unsigned_to_nat(3u);
if (v_isShared_5238_ == 0)
{
lean_ctor_set(v___x_5237_, 4, v_l_5211_);
lean_ctor_set(v___x_5237_, 3, v_l_5211_);
lean_ctor_set(v___x_5237_, 2, v_v_5230_);
lean_ctor_set(v___x_5237_, 1, v_k_5229_);
lean_ctor_set(v___x_5237_, 0, v___x_5125_);
v___x_5241_ = v___x_5237_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v___x_5125_);
lean_ctor_set(v_reuseFailAlloc_5248_, 1, v_k_5229_);
lean_ctor_set(v_reuseFailAlloc_5248_, 2, v_v_5230_);
lean_ctor_set(v_reuseFailAlloc_5248_, 3, v_l_5211_);
lean_ctor_set(v_reuseFailAlloc_5248_, 4, v_l_5211_);
v___x_5241_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
lean_object* v___x_5243_; 
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 4, v_l_5211_);
lean_ctor_set(v___x_5232_, 2, v_v_5117_);
lean_ctor_set(v___x_5232_, 1, v_k_5116_);
lean_ctor_set(v___x_5232_, 0, v___x_5125_);
v___x_5243_ = v___x_5232_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5125_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5247_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5247_, 3, v_l_5211_);
lean_ctor_set(v_reuseFailAlloc_5247_, 4, v_l_5211_);
v___x_5243_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
lean_object* v___x_5245_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v___x_5243_);
lean_ctor_set(v___x_5121_, 3, v___x_5241_);
lean_ctor_set(v___x_5121_, 2, v_v_5235_);
lean_ctor_set(v___x_5121_, 1, v_k_5234_);
lean_ctor_set(v___x_5121_, 0, v___x_5239_);
v___x_5245_ = v___x_5121_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5239_);
lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_k_5234_);
lean_ctor_set(v_reuseFailAlloc_5246_, 2, v_v_5235_);
lean_ctor_set(v_reuseFailAlloc_5246_, 3, v___x_5241_);
lean_ctor_set(v_reuseFailAlloc_5246_, 4, v___x_5243_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
}
}
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5259_; 
v___x_5257_ = lean_unsigned_to_nat(2u);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v_r_5228_);
lean_ctor_set(v___x_5121_, 3, v_impl_5124_);
lean_ctor_set(v___x_5121_, 0, v___x_5257_);
v___x_5259_ = v___x_5121_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5257_);
lean_ctor_set(v_reuseFailAlloc_5260_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5260_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5260_, 3, v_impl_5124_);
lean_ctor_set(v_reuseFailAlloc_5260_, 4, v_r_5228_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
case 1:
{
lean_object* v___x_5262_; 
lean_dec(v_v_5117_);
lean_dec(v_k_5116_);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 2, v_v_5113_);
lean_ctor_set(v___x_5121_, 1, v_k_5112_);
v___x_5262_ = v___x_5121_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_size_5115_);
lean_ctor_set(v_reuseFailAlloc_5263_, 1, v_k_5112_);
lean_ctor_set(v_reuseFailAlloc_5263_, 2, v_v_5113_);
lean_ctor_set(v_reuseFailAlloc_5263_, 3, v_l_5118_);
lean_ctor_set(v_reuseFailAlloc_5263_, 4, v_r_5119_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
default: 
{
lean_object* v_impl_5264_; lean_object* v___x_5265_; 
lean_dec(v_size_5115_);
v_impl_5264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5112_, v_v_5113_, v_r_5119_);
v___x_5265_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5118_) == 0)
{
lean_object* v_size_5266_; lean_object* v_size_5267_; lean_object* v_k_5268_; lean_object* v_v_5269_; lean_object* v_l_5270_; lean_object* v_r_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; uint8_t v___x_5274_; 
v_size_5266_ = lean_ctor_get(v_l_5118_, 0);
v_size_5267_ = lean_ctor_get(v_impl_5264_, 0);
v_k_5268_ = lean_ctor_get(v_impl_5264_, 1);
v_v_5269_ = lean_ctor_get(v_impl_5264_, 2);
v_l_5270_ = lean_ctor_get(v_impl_5264_, 3);
lean_inc(v_l_5270_);
v_r_5271_ = lean_ctor_get(v_impl_5264_, 4);
v___x_5272_ = lean_unsigned_to_nat(3u);
v___x_5273_ = lean_nat_mul(v___x_5272_, v_size_5266_);
v___x_5274_ = lean_nat_dec_lt(v___x_5273_, v_size_5267_);
lean_dec(v___x_5273_);
if (v___x_5274_ == 0)
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5278_; 
lean_dec(v_l_5270_);
v___x_5275_ = lean_nat_add(v___x_5265_, v_size_5266_);
v___x_5276_ = lean_nat_add(v___x_5275_, v_size_5267_);
lean_dec(v___x_5275_);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v_impl_5264_);
lean_ctor_set(v___x_5121_, 0, v___x_5276_);
v___x_5278_ = v___x_5121_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5276_);
lean_ctor_set(v_reuseFailAlloc_5279_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5279_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5279_, 3, v_l_5118_);
lean_ctor_set(v_reuseFailAlloc_5279_, 4, v_impl_5264_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
else
{
lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5343_; 
lean_inc(v_r_5271_);
lean_inc(v_v_5269_);
lean_inc(v_k_5268_);
lean_inc(v_size_5267_);
v_isSharedCheck_5343_ = !lean_is_exclusive(v_impl_5264_);
if (v_isSharedCheck_5343_ == 0)
{
lean_object* v_unused_5344_; lean_object* v_unused_5345_; lean_object* v_unused_5346_; lean_object* v_unused_5347_; lean_object* v_unused_5348_; 
v_unused_5344_ = lean_ctor_get(v_impl_5264_, 4);
lean_dec(v_unused_5344_);
v_unused_5345_ = lean_ctor_get(v_impl_5264_, 3);
lean_dec(v_unused_5345_);
v_unused_5346_ = lean_ctor_get(v_impl_5264_, 2);
lean_dec(v_unused_5346_);
v_unused_5347_ = lean_ctor_get(v_impl_5264_, 1);
lean_dec(v_unused_5347_);
v_unused_5348_ = lean_ctor_get(v_impl_5264_, 0);
lean_dec(v_unused_5348_);
v___x_5281_ = v_impl_5264_;
v_isShared_5282_ = v_isSharedCheck_5343_;
goto v_resetjp_5280_;
}
else
{
lean_dec(v_impl_5264_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5343_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v_size_5283_; lean_object* v_k_5284_; lean_object* v_v_5285_; lean_object* v_l_5286_; lean_object* v_r_5287_; lean_object* v_size_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; uint8_t v___x_5291_; 
v_size_5283_ = lean_ctor_get(v_l_5270_, 0);
v_k_5284_ = lean_ctor_get(v_l_5270_, 1);
v_v_5285_ = lean_ctor_get(v_l_5270_, 2);
v_l_5286_ = lean_ctor_get(v_l_5270_, 3);
v_r_5287_ = lean_ctor_get(v_l_5270_, 4);
v_size_5288_ = lean_ctor_get(v_r_5271_, 0);
v___x_5289_ = lean_unsigned_to_nat(2u);
v___x_5290_ = lean_nat_mul(v___x_5289_, v_size_5288_);
v___x_5291_ = lean_nat_dec_lt(v_size_5283_, v___x_5290_);
lean_dec(v___x_5290_);
if (v___x_5291_ == 0)
{
lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5319_; 
lean_inc(v_r_5287_);
lean_inc(v_l_5286_);
lean_inc(v_v_5285_);
lean_inc(v_k_5284_);
v_isSharedCheck_5319_ = !lean_is_exclusive(v_l_5270_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; lean_object* v_unused_5321_; lean_object* v_unused_5322_; lean_object* v_unused_5323_; lean_object* v_unused_5324_; 
v_unused_5320_ = lean_ctor_get(v_l_5270_, 4);
lean_dec(v_unused_5320_);
v_unused_5321_ = lean_ctor_get(v_l_5270_, 3);
lean_dec(v_unused_5321_);
v_unused_5322_ = lean_ctor_get(v_l_5270_, 2);
lean_dec(v_unused_5322_);
v_unused_5323_ = lean_ctor_get(v_l_5270_, 1);
lean_dec(v_unused_5323_);
v_unused_5324_ = lean_ctor_get(v_l_5270_, 0);
lean_dec(v_unused_5324_);
v___x_5293_ = v_l_5270_;
v_isShared_5294_ = v_isSharedCheck_5319_;
goto v_resetjp_5292_;
}
else
{
lean_dec(v_l_5270_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5319_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___y_5298_; lean_object* v___y_5299_; lean_object* v___y_5300_; lean_object* v___y_5309_; 
v___x_5295_ = lean_nat_add(v___x_5265_, v_size_5266_);
v___x_5296_ = lean_nat_add(v___x_5295_, v_size_5267_);
lean_dec(v_size_5267_);
if (lean_obj_tag(v_l_5286_) == 0)
{
lean_object* v_size_5317_; 
v_size_5317_ = lean_ctor_get(v_l_5286_, 0);
lean_inc(v_size_5317_);
v___y_5309_ = v_size_5317_;
goto v___jp_5308_;
}
else
{
lean_object* v___x_5318_; 
v___x_5318_ = lean_unsigned_to_nat(0u);
v___y_5309_ = v___x_5318_;
goto v___jp_5308_;
}
v___jp_5297_:
{
lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5301_ = lean_nat_add(v___y_5298_, v___y_5300_);
lean_dec(v___y_5300_);
lean_dec(v___y_5298_);
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 4, v_r_5271_);
lean_ctor_set(v___x_5293_, 3, v_r_5287_);
lean_ctor_set(v___x_5293_, 2, v_v_5269_);
lean_ctor_set(v___x_5293_, 1, v_k_5268_);
lean_ctor_set(v___x_5293_, 0, v___x_5301_);
v___x_5303_ = v___x_5293_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v___x_5301_);
lean_ctor_set(v_reuseFailAlloc_5307_, 1, v_k_5268_);
lean_ctor_set(v_reuseFailAlloc_5307_, 2, v_v_5269_);
lean_ctor_set(v_reuseFailAlloc_5307_, 3, v_r_5287_);
lean_ctor_set(v_reuseFailAlloc_5307_, 4, v_r_5271_);
v___x_5303_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5305_; 
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 4, v___x_5303_);
lean_ctor_set(v___x_5281_, 3, v___y_5299_);
lean_ctor_set(v___x_5281_, 2, v_v_5285_);
lean_ctor_set(v___x_5281_, 1, v_k_5284_);
lean_ctor_set(v___x_5281_, 0, v___x_5296_);
v___x_5305_ = v___x_5281_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5296_);
lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_k_5284_);
lean_ctor_set(v_reuseFailAlloc_5306_, 2, v_v_5285_);
lean_ctor_set(v_reuseFailAlloc_5306_, 3, v___y_5299_);
lean_ctor_set(v_reuseFailAlloc_5306_, 4, v___x_5303_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
v___jp_5308_:
{
lean_object* v___x_5310_; lean_object* v___x_5312_; 
v___x_5310_ = lean_nat_add(v___x_5295_, v___y_5309_);
lean_dec(v___y_5309_);
lean_dec(v___x_5295_);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v_l_5286_);
lean_ctor_set(v___x_5121_, 0, v___x_5310_);
v___x_5312_ = v___x_5121_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5310_);
lean_ctor_set(v_reuseFailAlloc_5316_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5316_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5316_, 3, v_l_5118_);
lean_ctor_set(v_reuseFailAlloc_5316_, 4, v_l_5286_);
v___x_5312_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
lean_object* v___x_5313_; 
v___x_5313_ = lean_nat_add(v___x_5265_, v_size_5288_);
if (lean_obj_tag(v_r_5287_) == 0)
{
lean_object* v_size_5314_; 
v_size_5314_ = lean_ctor_get(v_r_5287_, 0);
lean_inc(v_size_5314_);
v___y_5298_ = v___x_5313_;
v___y_5299_ = v___x_5312_;
v___y_5300_ = v_size_5314_;
goto v___jp_5297_;
}
else
{
lean_object* v___x_5315_; 
v___x_5315_ = lean_unsigned_to_nat(0u);
v___y_5298_ = v___x_5313_;
v___y_5299_ = v___x_5312_;
v___y_5300_ = v___x_5315_;
goto v___jp_5297_;
}
}
}
}
}
else
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5329_; 
lean_del_object(v___x_5121_);
v___x_5325_ = lean_nat_add(v___x_5265_, v_size_5266_);
v___x_5326_ = lean_nat_add(v___x_5325_, v_size_5267_);
lean_dec(v_size_5267_);
v___x_5327_ = lean_nat_add(v___x_5325_, v_size_5283_);
lean_dec(v___x_5325_);
lean_inc_ref(v_l_5118_);
if (v_isShared_5282_ == 0)
{
lean_ctor_set(v___x_5281_, 4, v_l_5270_);
lean_ctor_set(v___x_5281_, 3, v_l_5118_);
lean_ctor_set(v___x_5281_, 2, v_v_5117_);
lean_ctor_set(v___x_5281_, 1, v_k_5116_);
lean_ctor_set(v___x_5281_, 0, v___x_5327_);
v___x_5329_ = v___x_5281_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v___x_5327_);
lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5342_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5342_, 3, v_l_5118_);
lean_ctor_set(v_reuseFailAlloc_5342_, 4, v_l_5270_);
v___x_5329_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
v_isSharedCheck_5336_ = !lean_is_exclusive(v_l_5118_);
if (v_isSharedCheck_5336_ == 0)
{
lean_object* v_unused_5337_; lean_object* v_unused_5338_; lean_object* v_unused_5339_; lean_object* v_unused_5340_; lean_object* v_unused_5341_; 
v_unused_5337_ = lean_ctor_get(v_l_5118_, 4);
lean_dec(v_unused_5337_);
v_unused_5338_ = lean_ctor_get(v_l_5118_, 3);
lean_dec(v_unused_5338_);
v_unused_5339_ = lean_ctor_get(v_l_5118_, 2);
lean_dec(v_unused_5339_);
v_unused_5340_ = lean_ctor_get(v_l_5118_, 1);
lean_dec(v_unused_5340_);
v_unused_5341_ = lean_ctor_get(v_l_5118_, 0);
lean_dec(v_unused_5341_);
v___x_5331_ = v_l_5118_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_dec(v_l_5118_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
lean_ctor_set(v___x_5331_, 4, v_r_5271_);
lean_ctor_set(v___x_5331_, 3, v___x_5329_);
lean_ctor_set(v___x_5331_, 2, v_v_5269_);
lean_ctor_set(v___x_5331_, 1, v_k_5268_);
lean_ctor_set(v___x_5331_, 0, v___x_5326_);
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5326_);
lean_ctor_set(v_reuseFailAlloc_5335_, 1, v_k_5268_);
lean_ctor_set(v_reuseFailAlloc_5335_, 2, v_v_5269_);
lean_ctor_set(v_reuseFailAlloc_5335_, 3, v___x_5329_);
lean_ctor_set(v_reuseFailAlloc_5335_, 4, v_r_5271_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5349_; 
v_l_5349_ = lean_ctor_get(v_impl_5264_, 3);
lean_inc(v_l_5349_);
if (lean_obj_tag(v_l_5349_) == 0)
{
lean_object* v_r_5350_; lean_object* v_k_5351_; lean_object* v_v_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5375_; 
v_r_5350_ = lean_ctor_get(v_impl_5264_, 4);
v_k_5351_ = lean_ctor_get(v_impl_5264_, 1);
v_v_5352_ = lean_ctor_get(v_impl_5264_, 2);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_impl_5264_);
if (v_isSharedCheck_5375_ == 0)
{
lean_object* v_unused_5376_; lean_object* v_unused_5377_; 
v_unused_5376_ = lean_ctor_get(v_impl_5264_, 3);
lean_dec(v_unused_5376_);
v_unused_5377_ = lean_ctor_get(v_impl_5264_, 0);
lean_dec(v_unused_5377_);
v___x_5354_ = v_impl_5264_;
v_isShared_5355_ = v_isSharedCheck_5375_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_r_5350_);
lean_inc(v_v_5352_);
lean_inc(v_k_5351_);
lean_dec(v_impl_5264_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5375_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v_k_5356_; lean_object* v_v_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5371_; 
v_k_5356_ = lean_ctor_get(v_l_5349_, 1);
v_v_5357_ = lean_ctor_get(v_l_5349_, 2);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_l_5349_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; lean_object* v_unused_5373_; lean_object* v_unused_5374_; 
v_unused_5372_ = lean_ctor_get(v_l_5349_, 4);
lean_dec(v_unused_5372_);
v_unused_5373_ = lean_ctor_get(v_l_5349_, 3);
lean_dec(v_unused_5373_);
v_unused_5374_ = lean_ctor_get(v_l_5349_, 0);
lean_dec(v_unused_5374_);
v___x_5359_ = v_l_5349_;
v_isShared_5360_ = v_isSharedCheck_5371_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_v_5357_);
lean_inc(v_k_5356_);
lean_dec(v_l_5349_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5371_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5361_; lean_object* v___x_5363_; 
v___x_5361_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5350_, 2);
if (v_isShared_5360_ == 0)
{
lean_ctor_set(v___x_5359_, 4, v_r_5350_);
lean_ctor_set(v___x_5359_, 3, v_r_5350_);
lean_ctor_set(v___x_5359_, 2, v_v_5117_);
lean_ctor_set(v___x_5359_, 1, v_k_5116_);
lean_ctor_set(v___x_5359_, 0, v___x_5265_);
v___x_5363_ = v___x_5359_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5370_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5370_, 3, v_r_5350_);
lean_ctor_set(v_reuseFailAlloc_5370_, 4, v_r_5350_);
v___x_5363_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
lean_object* v___x_5365_; 
lean_inc(v_r_5350_);
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 3, v_r_5350_);
lean_ctor_set(v___x_5354_, 0, v___x_5265_);
v___x_5365_ = v___x_5354_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5369_, 1, v_k_5351_);
lean_ctor_set(v_reuseFailAlloc_5369_, 2, v_v_5352_);
lean_ctor_set(v_reuseFailAlloc_5369_, 3, v_r_5350_);
lean_ctor_set(v_reuseFailAlloc_5369_, 4, v_r_5350_);
v___x_5365_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
lean_object* v___x_5367_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v___x_5365_);
lean_ctor_set(v___x_5121_, 3, v___x_5363_);
lean_ctor_set(v___x_5121_, 2, v_v_5357_);
lean_ctor_set(v___x_5121_, 1, v_k_5356_);
lean_ctor_set(v___x_5121_, 0, v___x_5361_);
v___x_5367_ = v___x_5121_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5368_, 1, v_k_5356_);
lean_ctor_set(v_reuseFailAlloc_5368_, 2, v_v_5357_);
lean_ctor_set(v_reuseFailAlloc_5368_, 3, v___x_5363_);
lean_ctor_set(v_reuseFailAlloc_5368_, 4, v___x_5365_);
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
}
}
else
{
lean_object* v_r_5378_; 
v_r_5378_ = lean_ctor_get(v_impl_5264_, 4);
lean_inc(v_r_5378_);
if (lean_obj_tag(v_r_5378_) == 0)
{
lean_object* v_k_5379_; lean_object* v_v_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5391_; 
v_k_5379_ = lean_ctor_get(v_impl_5264_, 1);
v_v_5380_ = lean_ctor_get(v_impl_5264_, 2);
v_isSharedCheck_5391_ = !lean_is_exclusive(v_impl_5264_);
if (v_isSharedCheck_5391_ == 0)
{
lean_object* v_unused_5392_; lean_object* v_unused_5393_; lean_object* v_unused_5394_; 
v_unused_5392_ = lean_ctor_get(v_impl_5264_, 4);
lean_dec(v_unused_5392_);
v_unused_5393_ = lean_ctor_get(v_impl_5264_, 3);
lean_dec(v_unused_5393_);
v_unused_5394_ = lean_ctor_get(v_impl_5264_, 0);
lean_dec(v_unused_5394_);
v___x_5382_ = v_impl_5264_;
v_isShared_5383_ = v_isSharedCheck_5391_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_v_5380_);
lean_inc(v_k_5379_);
lean_dec(v_impl_5264_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5391_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5384_; lean_object* v___x_5386_; 
v___x_5384_ = lean_unsigned_to_nat(3u);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 4, v_l_5349_);
lean_ctor_set(v___x_5382_, 2, v_v_5117_);
lean_ctor_set(v___x_5382_, 1, v_k_5116_);
lean_ctor_set(v___x_5382_, 0, v___x_5265_);
v___x_5386_ = v___x_5382_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5390_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5390_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5390_, 3, v_l_5349_);
lean_ctor_set(v_reuseFailAlloc_5390_, 4, v_l_5349_);
v___x_5386_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
lean_object* v___x_5388_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v_r_5378_);
lean_ctor_set(v___x_5121_, 3, v___x_5386_);
lean_ctor_set(v___x_5121_, 2, v_v_5380_);
lean_ctor_set(v___x_5121_, 1, v_k_5379_);
lean_ctor_set(v___x_5121_, 0, v___x_5384_);
v___x_5388_ = v___x_5121_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v___x_5384_);
lean_ctor_set(v_reuseFailAlloc_5389_, 1, v_k_5379_);
lean_ctor_set(v_reuseFailAlloc_5389_, 2, v_v_5380_);
lean_ctor_set(v_reuseFailAlloc_5389_, 3, v___x_5386_);
lean_ctor_set(v_reuseFailAlloc_5389_, 4, v_r_5378_);
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
else
{
lean_object* v___x_5395_; lean_object* v___x_5397_; 
v___x_5395_ = lean_unsigned_to_nat(2u);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 4, v_impl_5264_);
lean_ctor_set(v___x_5121_, 3, v_r_5378_);
lean_ctor_set(v___x_5121_, 0, v___x_5395_);
v___x_5397_ = v___x_5121_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v___x_5395_);
lean_ctor_set(v_reuseFailAlloc_5398_, 1, v_k_5116_);
lean_ctor_set(v_reuseFailAlloc_5398_, 2, v_v_5117_);
lean_ctor_set(v_reuseFailAlloc_5398_, 3, v_r_5378_);
lean_ctor_set(v_reuseFailAlloc_5398_, 4, v_impl_5264_);
v___x_5397_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
return v___x_5397_;
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
lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5400_ = lean_unsigned_to_nat(1u);
v___x_5401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5400_);
lean_ctor_set(v___x_5401_, 1, v_k_5112_);
lean_ctor_set(v___x_5401_, 2, v_v_5113_);
lean_ctor_set(v___x_5401_, 3, v_t_5114_);
lean_ctor_set(v___x_5401_, 4, v_t_5114_);
return v___x_5401_;
}
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(lean_object* v_init_5403_, lean_object* v_x_5404_){
_start:
{
lean_object* v_d_5407_; 
if (lean_obj_tag(v_x_5404_) == 0)
{
lean_object* v_k_5410_; lean_object* v_v_5411_; lean_object* v_l_5412_; lean_object* v_r_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
v_k_5410_ = lean_ctor_get(v_x_5404_, 1);
v_v_5411_ = lean_ctor_get(v_x_5404_, 2);
v_l_5412_ = lean_ctor_get(v_x_5404_, 3);
v_r_5413_ = lean_ctor_get(v_x_5404_, 4);
v___x_5414_ = lean_box(0);
v___x_5415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5416_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5403_, v_l_5412_);
if (lean_obj_tag(v___x_5416_) == 0)
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5452_; 
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
v_isSharedCheck_5452_ = !lean_is_exclusive(v___x_5416_);
if (v_isSharedCheck_5452_ == 0)
{
v___x_5419_ = v___x_5416_;
v_isShared_5420_ = v_isSharedCheck_5452_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___x_5416_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5452_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
if (lean_obj_tag(v_a_5417_) == 0)
{
lean_object* v_a_5421_; 
lean_del_object(v___x_5419_);
v_a_5421_ = lean_ctor_get(v_a_5417_, 0);
lean_inc(v_a_5421_);
lean_dec_ref_known(v_a_5417_, 1);
v_d_5407_ = v_a_5421_;
goto v___jp_5406_;
}
else
{
lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5450_; 
v_isSharedCheck_5450_ = !lean_is_exclusive(v_a_5417_);
if (v_isSharedCheck_5450_ == 0)
{
lean_object* v_unused_5451_; 
v_unused_5451_ = lean_ctor_get(v_a_5417_, 0);
lean_dec(v_unused_5451_);
v___x_5423_ = v_a_5417_;
v_isShared_5424_ = v_isSharedCheck_5450_;
goto v_resetjp_5422_;
}
else
{
lean_dec(v_a_5417_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5450_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5425_; lean_object* v___x_5426_; uint8_t v___x_5427_; 
v___x_5425_ = lean_array_get_size(v_v_5411_);
v___x_5426_ = lean_unsigned_to_nat(0u);
v___x_5427_ = lean_nat_dec_eq(v___x_5425_, v___x_5426_);
if (v___x_5427_ == 0)
{
lean_del_object(v___x_5423_);
lean_del_object(v___x_5419_);
v_init_5403_ = v___x_5415_;
v_x_5404_ = v_r_5413_;
goto _start;
}
else
{
lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5429_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__1));
v___x_5430_ = lean_string_append(v___x_5429_, v_k_5410_);
v___x_5431_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___closed__0));
v___x_5432_ = lean_string_append(v___x_5430_, v___x_5431_);
v___x_5433_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5432_);
lean_dec_ref(v___x_5432_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v_a_5434_; lean_object* v___x_5436_; 
v_a_5434_ = lean_ctor_get(v___x_5433_, 0);
lean_inc(v_a_5434_);
lean_dec_ref_known(v___x_5433_, 1);
if (v_isShared_5424_ == 0)
{
lean_ctor_set_tag(v___x_5423_, 0);
lean_ctor_set(v___x_5423_, 0, v_a_5434_);
v___x_5436_ = v___x_5423_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_a_5434_);
v___x_5436_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
lean_object* v___x_5438_; 
if (v_isShared_5420_ == 0)
{
lean_ctor_set_tag(v___x_5419_, 1);
lean_ctor_set(v___x_5419_, 0, v___x_5436_);
v___x_5438_ = v___x_5419_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5436_);
v___x_5438_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
lean_object* v___x_5439_; 
v___x_5439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5439_, 0, v___x_5438_);
lean_ctor_set(v___x_5439_, 1, v___x_5414_);
v_d_5407_ = v___x_5439_;
goto v___jp_5406_;
}
}
}
else
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
lean_del_object(v___x_5423_);
lean_del_object(v___x_5419_);
v_a_5442_ = lean_ctor_get(v___x_5433_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5433_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5444_ = v___x_5433_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5433_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5447_; 
if (v_isShared_5445_ == 0)
{
v___x_5447_ = v___x_5444_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5442_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
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
return v___x_5416_;
}
}
else
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5453_, 0, v_init_5403_);
v___x_5454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5453_);
return v___x_5454_;
}
v___jp_5406_:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5408_, 0, v_d_5407_);
v___x_5409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5408_);
return v___x_5409_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_5403_ = stack[0].m_obj;
lean_object* v_x_5404_ = stack[1].m_obj;
lean_object* v_res_5455_;
v_res_5455_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5403_, v_x_5404_);
stack->m_obj
 = v_res_5455_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2___boxed(lean_object* v_init_5456_, lean_object* v_x_5457_, lean_object* v___y_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v_init_5456_, v_x_5457_);
lean_dec(v_x_5457_);
return v_res_5459_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(lean_object* v_cfg_5465_){
_start:
{
lean_object* v___y_5468_; lean_object* v_a_5469_; lean_object* v___y_5482_; lean_object* v_externalKernels_5483_; lean_object* v___y_5496_; lean_object* v___y_5497_; uint8_t v___y_5498_; lean_object* v_a_5499_; lean_object* v___y_5513_; uint8_t v___y_5514_; lean_object* v_enable__nanoda_x3f_5527_; lean_object* v_external__kernels_x3f_5528_; lean_object* v___y_5530_; 
v_enable__nanoda_x3f_5527_ = lean_ctor_get(v_cfg_5465_, 5);
lean_inc(v_enable__nanoda_x3f_5527_);
v_external__kernels_x3f_5528_ = lean_ctor_get(v_cfg_5465_, 6);
lean_inc(v_external__kernels_x3f_5528_);
lean_dec_ref(v_cfg_5465_);
if (lean_obj_tag(v_external__kernels_x3f_5528_) == 0)
{
lean_object* v___x_5561_; 
v___x_5561_ = lean_box(1);
v___y_5530_ = v___x_5561_;
goto v___jp_5529_;
}
else
{
lean_object* v_val_5562_; 
v_val_5562_ = lean_ctor_get(v_external__kernels_x3f_5528_, 0);
lean_inc(v_val_5562_);
lean_dec_ref_known(v_external__kernels_x3f_5528_, 1);
v___y_5530_ = v_val_5562_;
goto v___jp_5529_;
}
v___jp_5467_:
{
lean_object* v_fst_5470_; 
v_fst_5470_ = lean_ctor_get(v_a_5469_, 0);
lean_inc(v_fst_5470_);
lean_dec_ref(v_a_5469_);
if (lean_obj_tag(v_fst_5470_) == 0)
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5471_, 0, v___y_5468_);
v___x_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5472_, 0, v___x_5471_);
return v___x_5472_;
}
else
{
lean_object* v_val_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5480_; 
lean_dec(v___y_5468_);
v_val_5473_ = lean_ctor_get(v_fst_5470_, 0);
v_isSharedCheck_5480_ = !lean_is_exclusive(v_fst_5470_);
if (v_isSharedCheck_5480_ == 0)
{
v___x_5475_ = v_fst_5470_;
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_val_5473_);
lean_dec(v_fst_5470_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5480_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5478_; 
if (v_isShared_5476_ == 0)
{
lean_ctor_set_tag(v___x_5475_, 0);
v___x_5478_ = v___x_5475_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_val_5473_);
v___x_5478_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
return v___x_5478_;
}
}
}
}
v___jp_5481_:
{
lean_object* v___x_5484_; 
v___x_5484_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0(v___y_5482_, v_externalKernels_5483_);
if (lean_obj_tag(v___x_5484_) == 0)
{
lean_object* v_a_5485_; lean_object* v_a_5486_; 
v_a_5485_ = lean_ctor_get(v___x_5484_, 0);
lean_inc(v_a_5485_);
lean_dec_ref_known(v___x_5484_, 1);
v_a_5486_ = lean_ctor_get(v_a_5485_, 0);
lean_inc(v_a_5486_);
lean_dec(v_a_5485_);
v___y_5468_ = v_externalKernels_5483_;
v_a_5469_ = v_a_5486_;
goto v___jp_5467_;
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec(v_externalKernels_5483_);
v_a_5487_ = lean_ctor_get(v___x_5484_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5484_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5484_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5484_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
v___jp_5495_:
{
lean_object* v_fst_5500_; 
v_fst_5500_ = lean_ctor_get(v_a_5499_, 0);
lean_inc(v_fst_5500_);
lean_dec_ref(v_a_5499_);
if (lean_obj_tag(v_fst_5500_) == 0)
{
if (v___y_5498_ == 0)
{
v___y_5482_ = v___y_5496_;
v_externalKernels_5483_ = v___y_5497_;
goto v___jp_5481_;
}
else
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; 
v___x_5501_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_bundledKernels___closed__4));
v___x_5502_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__0));
v___x_5503_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v___x_5501_, v___x_5502_, v___y_5497_);
v___y_5482_ = v___y_5496_;
v_externalKernels_5483_ = v___x_5503_;
goto v___jp_5481_;
}
}
else
{
lean_object* v_val_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec(v___y_5497_);
lean_dec_ref(v___y_5496_);
v_val_5504_ = lean_ctor_get(v_fst_5500_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v_fst_5500_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v_fst_5500_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_val_5504_);
lean_dec(v_fst_5500_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
lean_ctor_set_tag(v___x_5506_, 0);
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_val_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
v___jp_5512_:
{
lean_object* v___x_5515_; lean_object* v___x_5516_; 
v___x_5515_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__0___closed__0));
v___x_5516_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__2(v___x_5515_, v___y_5513_);
if (lean_obj_tag(v___x_5516_) == 0)
{
lean_object* v_a_5517_; lean_object* v_a_5518_; 
v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
lean_inc(v_a_5517_);
lean_dec_ref_known(v___x_5516_, 1);
v_a_5518_ = lean_ctor_get(v_a_5517_, 0);
lean_inc(v_a_5518_);
lean_dec(v_a_5517_);
v___y_5496_ = v___x_5515_;
v___y_5497_ = v___y_5513_;
v___y_5498_ = v___y_5514_;
v_a_5499_ = v_a_5518_;
goto v___jp_5495_;
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_dec(v___y_5513_);
v_a_5519_ = lean_ctor_get(v___x_5516_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5516_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5516_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5516_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
v___jp_5529_:
{
if (lean_obj_tag(v_enable__nanoda_x3f_5527_) == 0)
{
uint8_t v___x_5531_; 
v___x_5531_ = 0;
v___y_5513_ = v___y_5530_;
v___y_5514_ = v___x_5531_;
goto v___jp_5512_;
}
else
{
lean_object* v_val_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5560_; 
v_val_5532_ = lean_ctor_get(v_enable__nanoda_x3f_5527_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v_enable__nanoda_x3f_5527_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5534_ = v_enable__nanoda_x3f_5527_;
v_isShared_5535_ = v_isSharedCheck_5560_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_val_5532_);
lean_dec(v_enable__nanoda_x3f_5527_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5560_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
uint8_t v___x_5536_; 
v___x_5536_ = lean_unbox(v_val_5532_);
if (v___x_5536_ == 0)
{
uint8_t v___x_5537_; 
lean_del_object(v___x_5534_);
v___x_5537_ = lean_unbox(v_val_5532_);
lean_dec(v_val_5532_);
v___y_5513_ = v___y_5530_;
v___y_5514_ = v___x_5537_;
goto v___jp_5512_;
}
else
{
if (lean_obj_tag(v___y_5530_) == 0)
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
lean_dec_ref_known(v___y_5530_, 5);
lean_dec(v_val_5532_);
v___x_5538_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___closed__1));
v___x_5539_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5538_);
if (lean_obj_tag(v___x_5539_) == 0)
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5550_; 
v_a_5540_ = lean_ctor_get(v___x_5539_, 0);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5542_ = v___x_5539_;
v_isShared_5543_ = v_isSharedCheck_5550_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5539_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5550_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5535_ == 0)
{
lean_ctor_set_tag(v___x_5534_, 0);
lean_ctor_set(v___x_5534_, 0, v_a_5540_);
v___x_5545_ = v___x_5534_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
lean_object* v___x_5547_; 
if (v_isShared_5543_ == 0)
{
lean_ctor_set(v___x_5542_, 0, v___x_5545_);
v___x_5547_ = v___x_5542_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5545_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_del_object(v___x_5534_);
v_a_5551_ = lean_ctor_get(v___x_5539_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5539_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5539_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5539_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
else
{
uint8_t v___x_5559_; 
lean_del_object(v___x_5534_);
v___x_5559_ = lean_unbox(v_val_5532_);
lean_dec(v_val_5532_);
v___y_5513_ = v___y_5530_;
v___y_5514_ = v___x_5559_;
goto v___jp_5512_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_5465_ = stack[0].m_obj;
lean_object* v_res_5563_;
v_res_5563_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_5465_);
stack->m_obj
 = v_res_5563_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels___boxed(lean_object* v_cfg_5564_, lean_object* v_a_5565_){
_start:
{
lean_object* v_res_5566_; 
v_res_5566_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v_cfg_5564_);
return v_res_5566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1(lean_object* v_00_u03b2_5567_, lean_object* v_k_5568_, lean_object* v_v_5569_, lean_object* v_t_5570_, lean_object* v_hl_5571_){
_start:
{
lean_object* v___x_5572_; 
v___x_5572_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels_spec__1___redArg(v_k_5568_, v_v_5569_, v_t_5570_);
return v___x_5572_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(lean_object* v_a_5590_, lean_object* v_a_5591_){
_start:
{
if (lean_obj_tag(v_a_5590_) == 0)
{
lean_object* v___x_5592_; 
v___x_5592_ = l_List_reverse___redArg(v_a_5591_);
return v___x_5592_;
}
else
{
lean_object* v_head_5593_; lean_object* v_tail_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5605_; 
v_head_5593_ = lean_ctor_get(v_a_5590_, 0);
v_tail_5594_ = lean_ctor_get(v_a_5590_, 1);
v_isSharedCheck_5605_ = !lean_is_exclusive(v_a_5590_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5596_ = v_a_5590_;
v_isShared_5597_ = v_isSharedCheck_5605_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_tail_5594_);
lean_inc(v_head_5593_);
lean_dec(v_a_5590_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5605_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v_fst_5598_; uint8_t v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5602_; 
v_fst_5598_ = lean_ctor_get(v_head_5593_, 0);
lean_inc(v_fst_5598_);
lean_dec(v_head_5593_);
v___x_5599_ = 1;
v___x_5600_ = l_Lean_Name_toString(v_fst_5598_, v___x_5599_);
if (v_isShared_5597_ == 0)
{
lean_ctor_set(v___x_5596_, 1, v_a_5591_);
lean_ctor_set(v___x_5596_, 0, v___x_5600_);
v___x_5602_ = v___x_5596_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5600_);
lean_ctor_set(v_reuseFailAlloc_5604_, 1, v_a_5591_);
v___x_5602_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
v_a_5590_ = v_tail_5594_;
v_a_5591_ = v___x_5602_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(lean_object* v_as_5606_, size_t v_i_5607_, size_t v_stop_5608_, lean_object* v_b_5609_){
_start:
{
lean_object* v___y_5611_; uint8_t v___x_5615_; 
v___x_5615_ = lean_usize_dec_eq(v_i_5607_, v_stop_5608_);
if (v___x_5615_ == 0)
{
lean_object* v___x_5616_; lean_object* v_fst_5617_; lean_object* v___x_5618_; uint8_t v___x_5619_; 
v___x_5616_ = lean_array_uget_borrowed(v_as_5606_, v_i_5607_);
v_fst_5617_ = lean_ctor_get(v___x_5616_, 0);
v___x_5618_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
v___x_5619_ = l_Array_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_builtinTargets_spec__0(v___x_5618_, v_fst_5617_);
if (v___x_5619_ == 0)
{
lean_object* v___x_5620_; 
lean_inc(v___x_5616_);
v___x_5620_ = lean_array_push(v_b_5609_, v___x_5616_);
v___y_5611_ = v___x_5620_;
goto v___jp_5610_;
}
else
{
v___y_5611_ = v_b_5609_;
goto v___jp_5610_;
}
}
else
{
return v_b_5609_;
}
v___jp_5610_:
{
size_t v___x_5612_; size_t v___x_5613_; 
v___x_5612_ = ((size_t)1ULL);
v___x_5613_ = lean_usize_add(v_i_5607_, v___x_5612_);
v_i_5607_ = v___x_5613_;
v_b_5609_ = v___y_5611_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5606_ = stack[0].m_obj;
size_t v_i_5607_ = stack[1].m_num;
size_t v_stop_5608_ = stack[2].m_num;
lean_object* v_b_5609_ = stack[3].m_obj;
lean_object* v_res_5621_;
v_res_5621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_5606_, v_i_5607_, v_stop_5608_, v_b_5609_);
stack->m_obj
 = v_res_5621_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1___boxed(lean_object* v_as_5622_, lean_object* v_i_5623_, lean_object* v_stop_5624_, lean_object* v_b_5625_){
_start:
{
size_t v_i_boxed_5626_; size_t v_stop_boxed_5627_; lean_object* v_res_5628_; 
v_i_boxed_5626_ = lean_unbox_usize(v_i_5623_);
lean_dec(v_i_5623_);
v_stop_boxed_5627_ = lean_unbox_usize(v_stop_5624_);
lean_dec(v_stop_5624_);
v_res_5628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_as_5622_, v_i_boxed_5626_, v_stop_boxed_5627_, v_b_5625_);
lean_dec_ref(v_as_5622_);
return v_res_5628_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(lean_object* v_a_5631_, lean_object* v_a_5632_){
_start:
{
if (lean_obj_tag(v_a_5631_) == 0)
{
lean_object* v___x_5633_; 
v___x_5633_ = l_List_reverse___redArg(v_a_5632_);
return v___x_5633_;
}
else
{
lean_object* v_head_5634_; lean_object* v_tail_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5655_; 
v_head_5634_ = lean_ctor_get(v_a_5631_, 0);
v_tail_5635_ = lean_ctor_get(v_a_5631_, 1);
v_isSharedCheck_5655_ = !lean_is_exclusive(v_a_5631_);
if (v_isSharedCheck_5655_ == 0)
{
v___x_5637_ = v_a_5631_;
v_isShared_5638_ = v_isSharedCheck_5655_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_tail_5635_);
lean_inc(v_head_5634_);
lean_dec(v_a_5631_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5655_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v_fst_5639_; lean_object* v_snd_5640_; lean_object* v___x_5641_; uint8_t v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5652_; 
v_fst_5639_ = lean_ctor_get(v_head_5634_, 0);
lean_inc(v_fst_5639_);
v_snd_5640_ = lean_ctor_get(v_head_5634_, 1);
lean_inc(v_snd_5640_);
lean_dec(v_head_5634_);
v___x_5641_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__0));
v___x_5642_ = 1;
v___x_5643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_5639_, v___x_5642_);
v___x_5644_ = lean_string_append(v___x_5641_, v___x_5643_);
lean_dec_ref(v___x_5643_);
v___x_5645_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0___closed__1));
v___x_5646_ = lean_string_append(v___x_5644_, v___x_5645_);
v___x_5647_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_snd_5640_, v___x_5642_);
v___x_5648_ = lean_string_append(v___x_5646_, v___x_5647_);
lean_dec_ref(v___x_5647_);
v___x_5649_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lake_Check_instFromJsonConfig_fromJson_spec__1_spec__1___closed__1));
v___x_5650_ = lean_string_append(v___x_5648_, v___x_5649_);
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v_a_5632_);
lean_ctor_set(v___x_5637_, 0, v___x_5650_);
v___x_5652_ = v___x_5637_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v___x_5650_);
lean_ctor_set(v_reuseFailAlloc_5654_, 1, v_a_5632_);
v___x_5652_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
v_a_5631_ = v_tail_5635_;
v_a_5632_ = v___x_5652_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(lean_object* v_exported_5661_){
_start:
{
lean_object* v___y_5664_; lean_object* v_used_5677_; lean_object* v___x_5690_; lean_object* v___x_5691_; uint8_t v___x_5692_; 
v_used_5677_ = l_Lake_Check_usedAxioms(v_exported_5661_);
v___x_5690_ = lean_array_get_size(v_used_5677_);
v___x_5691_ = lean_unsigned_to_nat(0u);
v___x_5692_ = lean_nat_dec_eq(v___x_5690_, v___x_5691_);
if (v___x_5692_ == 0)
{
lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
v___x_5693_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__2));
v___x_5694_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lake_CLI_Check_0__Lake_Check_withSafeExport_spec__0_spec__0___closed__0));
lean_inc_ref(v_used_5677_);
v___x_5695_ = lean_array_to_list(v_used_5677_);
v___x_5696_ = lean_box(0);
v___x_5697_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__2(v___x_5695_, v___x_5696_);
v___x_5698_ = l_String_intercalate(v___x_5694_, v___x_5697_);
v___x_5699_ = lean_string_append(v___x_5693_, v___x_5698_);
lean_dec_ref(v___x_5698_);
v___x_5700_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5699_);
if (lean_obj_tag(v___x_5700_) == 0)
{
lean_dec_ref_known(v___x_5700_, 1);
goto v___jp_5678_;
}
else
{
lean_dec_ref(v_used_5677_);
return v___x_5700_;
}
}
else
{
lean_object* v___x_5701_; lean_object* v___x_5702_; 
v___x_5701_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__3));
v___x_5702_ = l_IO_println___at___00__private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace_spec__2(v___x_5701_);
if (lean_obj_tag(v___x_5702_) == 0)
{
lean_dec_ref_known(v___x_5702_, 1);
goto v___jp_5678_;
}
else
{
lean_dec_ref(v_used_5677_);
return v___x_5702_;
}
}
v___jp_5663_:
{
lean_object* v___x_5665_; lean_object* v___x_5666_; uint8_t v___x_5667_; 
v___x_5665_ = lean_array_get_size(v___y_5664_);
v___x_5666_ = lean_unsigned_to_nat(0u);
v___x_5667_ = lean_nat_dec_eq(v___x_5665_, v___x_5666_);
if (v___x_5667_ == 0)
{
lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; 
v___x_5668_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__0));
v___x_5669_ = lean_array_to_list(v___y_5664_);
v___x_5670_ = lean_box(0);
v___x_5671_ = l_List_mapTR_loop___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__0(v___x_5669_, v___x_5670_);
v___x_5672_ = l_String_intercalate(v___x_5668_, v___x_5671_);
v___x_5673_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
v___x_5674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5674_, 0, v___x_5673_);
return v___x_5674_;
}
else
{
lean_object* v___x_5675_; lean_object* v___x_5676_; 
lean_dec_ref(v___y_5664_);
v___x_5675_ = lean_box(0);
v___x_5676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5675_);
return v___x_5676_;
}
}
v___jp_5678_:
{
lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; uint8_t v___x_5682_; 
v___x_5679_ = lean_unsigned_to_nat(0u);
v___x_5680_ = lean_array_get_size(v_used_5677_);
v___x_5681_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___closed__1));
v___x_5682_ = lean_nat_dec_lt(v___x_5679_, v___x_5680_);
if (v___x_5682_ == 0)
{
lean_dec_ref(v_used_5677_);
v___y_5664_ = v___x_5681_;
goto v___jp_5663_;
}
else
{
uint8_t v___x_5683_; 
v___x_5683_ = lean_nat_dec_le(v___x_5680_, v___x_5680_);
if (v___x_5683_ == 0)
{
if (v___x_5682_ == 0)
{
lean_dec_ref(v_used_5677_);
v___y_5664_ = v___x_5681_;
goto v___jp_5663_;
}
else
{
size_t v___x_5684_; size_t v___x_5685_; lean_object* v___x_5686_; 
v___x_5684_ = ((size_t)0ULL);
v___x_5685_ = lean_usize_of_nat(v___x_5680_);
v___x_5686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_5677_, v___x_5684_, v___x_5685_, v___x_5681_);
lean_dec_ref(v_used_5677_);
v___y_5664_ = v___x_5686_;
goto v___jp_5663_;
}
}
else
{
size_t v___x_5687_; size_t v___x_5688_; lean_object* v___x_5689_; 
v___x_5687_ = ((size_t)0ULL);
v___x_5688_ = lean_usize_of_nat(v___x_5680_);
v___x_5689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_spec__1(v_used_5677_, v___x_5687_, v___x_5688_, v___x_5681_);
lean_dec_ref(v_used_5677_);
v___y_5664_ = v___x_5689_;
goto v___jp_5663_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_exported_5661_ = stack[0].m_obj;
lean_object* v_res_5703_;
v_res_5703_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5661_);
stack->m_obj
 = v_res_5703_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg___boxed(lean_object* v_exported_5704_, lean_object* v_a_5705_){
_start:
{
lean_object* v_res_5706_; 
v_res_5706_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5704_);
return v_res_5706_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(lean_object* v_exported_5707_, lean_object* v_a_5708_){
_start:
{
lean_object* v___x_5710_; 
v___x_5710_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_exported_5707_);
return v___x_5710_;
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms_0interp(lean_interpreter_value* stack)
{
lean_object* v_exported_5707_ = stack[0].m_obj;
lean_object* v_a_5708_ = stack[1].m_obj;
lean_object* v_res_5711_;
v_res_5711_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_5707_, v_a_5708_);
stack->m_obj
 = v_res_5711_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___boxed(lean_object* v_exported_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_){
_start:
{
lean_object* v_res_5715_; 
v_res_5715_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms(v_exported_5712_, v_a_5713_);
lean_dec_ref(v_a_5713_);
return v_res_5715_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(lean_object* v_exportPath_5716_, lean_object* v___y_5717_){
_start:
{
lean_object* v___x_5719_; 
lean_inc_ref(v_exportPath_5716_);
v___x_5719_ = l___private_Lake_CLI_Check_0__Lake_Check_runKernels(v_exportPath_5716_, v___y_5717_);
if (lean_obj_tag(v___x_5719_) == 0)
{
uint8_t v___x_5720_; lean_object* v___x_5721_; 
lean_dec_ref_known(v___x_5719_, 1);
v___x_5720_ = 0;
v___x_5721_ = lean_io_prim_handle_mk(v_exportPath_5716_, v___x_5720_);
lean_dec_ref(v_exportPath_5716_);
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v_a_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; 
v_a_5722_ = lean_ctor_get(v___x_5721_, 0);
lean_inc(v_a_5722_);
lean_dec_ref_known(v___x_5721_, 1);
v___x_5723_ = lean_stream_of_handle(v_a_5722_);
v___x_5724_ = l_LeanExport_parseStream(v___x_5723_);
if (lean_obj_tag(v___x_5724_) == 0)
{
lean_object* v_a_5725_; lean_object* v___x_5726_; 
v_a_5725_ = lean_ctor_get(v___x_5724_, 0);
lean_inc(v_a_5725_);
lean_dec_ref_known(v___x_5724_, 1);
v___x_5726_ = l___private_Lake_CLI_Check_0__Lake_Check_checkUsedAxioms___redArg(v_a_5725_);
return v___x_5726_;
}
else
{
lean_object* v_a_5727_; lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5734_; 
v_a_5727_ = lean_ctor_get(v___x_5724_, 0);
v_isSharedCheck_5734_ = !lean_is_exclusive(v___x_5724_);
if (v_isSharedCheck_5734_ == 0)
{
v___x_5729_ = v___x_5724_;
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
else
{
lean_inc(v_a_5727_);
lean_dec(v___x_5724_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
lean_object* v___x_5732_; 
if (v_isShared_5730_ == 0)
{
v___x_5732_ = v___x_5729_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_a_5727_);
v___x_5732_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
return v___x_5732_;
}
}
}
}
else
{
lean_object* v_a_5735_; lean_object* v___x_5737_; uint8_t v_isShared_5738_; uint8_t v_isSharedCheck_5742_; 
v_a_5735_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5742_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5742_ == 0)
{
v___x_5737_ = v___x_5721_;
v_isShared_5738_ = v_isSharedCheck_5742_;
goto v_resetjp_5736_;
}
else
{
lean_inc(v_a_5735_);
lean_dec(v___x_5721_);
v___x_5737_ = lean_box(0);
v_isShared_5738_ = v_isSharedCheck_5742_;
goto v_resetjp_5736_;
}
v_resetjp_5736_:
{
lean_object* v___x_5740_; 
if (v_isShared_5738_ == 0)
{
v___x_5740_ = v___x_5737_;
goto v_reusejp_5739_;
}
else
{
lean_object* v_reuseFailAlloc_5741_; 
v_reuseFailAlloc_5741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5741_, 0, v_a_5735_);
v___x_5740_ = v_reuseFailAlloc_5741_;
goto v_reusejp_5739_;
}
v_reusejp_5739_:
{
return v___x_5740_;
}
}
}
}
else
{
lean_dec_ref(v_exportPath_5716_);
return v___x_5719_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_exportPath_5716_ = stack[0].m_obj;
lean_object* v___y_5717_ = stack[1].m_obj;
lean_object* v_res_5743_;
v_res_5743_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(v_exportPath_5716_, v___y_5717_);
stack->m_obj
 = v_res_5743_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0___boxed(lean_object* v_exportPath_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_){
_start:
{
lean_object* v_res_5747_; 
v_res_5747_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject___lam__0(v_exportPath_5744_, v___y_5745_);
lean_dec_ref(v___y_5745_);
return v_res_5747_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(lean_object* v_m_5748_, uint8_t v_a_5749_){
_start:
{
lean_object* v_buckets_5750_; lean_object* v___x_5751_; uint64_t v___x_5752_; uint64_t v___x_5753_; uint64_t v___x_5754_; uint64_t v_fold_5755_; uint64_t v___x_5756_; uint64_t v___x_5757_; uint64_t v___x_5758_; size_t v___x_5759_; size_t v___x_5760_; size_t v___x_5761_; size_t v___x_5762_; size_t v___x_5763_; lean_object* v___x_5764_; uint8_t v___x_5765_; 
v_buckets_5750_ = lean_ctor_get(v_m_5748_, 1);
v___x_5751_ = lean_array_get_size(v_buckets_5750_);
v___x_5752_ = l___private_Lake_CLI_Check_0__Lake_Check_instHashableModuleKind_hash(v_a_5749_);
v___x_5753_ = 32ULL;
v___x_5754_ = lean_uint64_shift_right(v___x_5752_, v___x_5753_);
v_fold_5755_ = lean_uint64_xor(v___x_5752_, v___x_5754_);
v___x_5756_ = 16ULL;
v___x_5757_ = lean_uint64_shift_right(v_fold_5755_, v___x_5756_);
v___x_5758_ = lean_uint64_xor(v_fold_5755_, v___x_5757_);
v___x_5759_ = lean_uint64_to_usize(v___x_5758_);
v___x_5760_ = lean_usize_of_nat(v___x_5751_);
v___x_5761_ = ((size_t)1ULL);
v___x_5762_ = lean_usize_sub(v___x_5760_, v___x_5761_);
v___x_5763_ = lean_usize_land(v___x_5759_, v___x_5762_);
v___x_5764_ = lean_array_uget_borrowed(v_buckets_5750_, v___x_5763_);
v___x_5765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore_spec__0_spec__0___redArg(v_a_5749_, v___x_5764_);
return v___x_5765_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_5748_ = stack[0].m_obj;
uint8_t v_a_5749_ = stack[1].m_num;
uint8_t v_res_5766_;
v_res_5766_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5748_, v_a_5749_);
stack->m_num = v_res_5766_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg___boxed(lean_object* v_m_5767_, lean_object* v_a_5768_){
_start:
{
uint8_t v_a_boxed_5769_; uint8_t v_res_5770_; lean_object* v_r_5771_; 
v_a_boxed_5769_ = lean_unbox(v_a_5768_);
v_res_5770_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5767_, v_a_boxed_5769_);
lean_dec_ref(v_m_5767_);
v_r_5771_ = lean_box(v_res_5770_);
return v_r_5771_;
}
}
lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject(lean_object* v_a_5773_){
_start:
{
lean_object* v_moduleStore_5775_; lean_object* v___f_5776_; uint8_t v___x_5777_; uint8_t v___x_5778_; 
v_moduleStore_5775_ = lean_ctor_get(v_a_5773_, 17);
v___f_5776_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_checkProject___closed__0));
v___x_5777_ = 0;
v___x_5778_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_moduleStore_5775_, v___x_5777_);
if (v___x_5778_ == 0)
{
lean_object* v___x_5779_; 
v___x_5779_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveDeps(v_a_5773_);
if (lean_obj_tag(v___x_5779_) == 0)
{
lean_object* v___x_5780_; 
lean_dec_ref_known(v___x_5779_, 1);
v___x_5780_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5776_, v_a_5773_);
return v___x_5780_;
}
else
{
return v___x_5779_;
}
}
else
{
lean_object* v___x_5781_; 
v___x_5781_ = l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg(v___f_5776_, v_a_5773_);
return v___x_5781_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Check_0__Lake_Check_checkProject_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5773_ = stack[0].m_obj;
lean_object* v_res_5782_;
v_res_5782_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_5773_);
stack->m_obj
 = v_res_5782_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Check_0__Lake_Check_checkProject___boxed(lean_object* v_a_5783_, lean_object* v_a_5784_){
_start:
{
lean_object* v_res_5785_; 
v_res_5785_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v_a_5783_);
lean_dec_ref(v_a_5783_);
return v_res_5785_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(lean_object* v_00_u03b2_5786_, lean_object* v_m_5787_, uint8_t v_a_5788_){
_start:
{
uint8_t v___x_5789_; 
v___x_5789_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_m_5787_, v_a_5788_);
return v___x_5789_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_5787_ = stack[1].m_obj;
uint8_t v_a_5788_ = stack[2].m_num;
uint8_t v_res_5790_;
v_res_5790_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(lean_box(0), v_m_5787_, v_a_5788_);
stack->m_num = v_res_5790_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___boxed(lean_object* v_00_u03b2_5791_, lean_object* v_m_5792_, lean_object* v_a_5793_){
_start:
{
uint8_t v_a_boxed_5794_; uint8_t v_res_5795_; lean_object* v_r_5796_; 
v_a_boxed_5794_ = lean_unbox(v_a_5793_);
v_res_5795_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0(v_00_u03b2_5791_, v_m_5792_, v_a_boxed_5794_);
lean_dec_ref(v_m_5792_);
v_r_5796_ = lean_box(v_res_5795_);
return v_r_5796_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_5797_; lean_object* v___x_5798_; 
v___x_5797_ = 0;
v___x_5798_ = lean_box_uint32(v___x_5797_);
return v___x_5798_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5799_; lean_object* v___x_5800_; 
v___x_5799_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
v___x_5800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5799_);
return v___x_5800_;
}
}
lean_object* l_Lake_Check_runComparator___lam__0(lean_object* v_____r_5801_){
_start:
{
lean_object* v___x_5803_; lean_object* v___x_5804_; 
v___x_5803_ = lean_obj_once(&l_Lake_Check_runComparator___lam__0___closed__0, &l_Lake_Check_runComparator___lam__0___closed__0_once, _init_l_Lake_Check_runComparator___lam__0___closed__0);
v___x_5804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5804_, 0, v___x_5803_);
return v___x_5804_;
}
}
LEAN_EXPORT void l_Lake_Check_runComparator___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_5801_ = stack[0].m_obj;
lean_object* v_res_5805_;
v_res_5805_ = l_Lake_Check_runComparator___lam__0(v_____r_5801_);
stack->m_obj
 = v_res_5805_;
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___lam__0___boxed(lean_object* v_____r_5806_, lean_object* v___y_5807_){
_start:
{
lean_object* v_res_5808_; 
v_res_5808_ = l_Lake_Check_runComparator___lam__0(v_____r_5806_);
return v_res_5808_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(size_t v_sz_5809_, size_t v_i_5810_, lean_object* v_bs_5811_){
_start:
{
uint8_t v___x_5812_; 
v___x_5812_ = lean_usize_dec_lt(v_i_5810_, v_sz_5809_);
if (v___x_5812_ == 0)
{
return v_bs_5811_;
}
else
{
lean_object* v_v_5813_; lean_object* v___x_5814_; lean_object* v_bs_x27_5815_; lean_object* v___x_5816_; size_t v___x_5817_; size_t v___x_5818_; lean_object* v___x_5819_; 
v_v_5813_ = lean_array_uget(v_bs_5811_, v_i_5810_);
v___x_5814_ = lean_unsigned_to_nat(0u);
v_bs_x27_5815_ = lean_array_uset(v_bs_5811_, v_i_5810_, v___x_5814_);
v___x_5816_ = l_String_toName(v_v_5813_);
v___x_5817_ = ((size_t)1ULL);
v___x_5818_ = lean_usize_add(v_i_5810_, v___x_5817_);
v___x_5819_ = lean_array_uset(v_bs_x27_5815_, v_i_5810_, v___x_5816_);
v_i_5810_ = v___x_5818_;
v_bs_5811_ = v___x_5819_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_5809_ = stack[0].m_num;
size_t v_i_5810_ = stack[1].m_num;
lean_object* v_bs_5811_ = stack[2].m_obj;
lean_object* v_res_5821_;
v_res_5821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5809_, v_i_5810_, v_bs_5811_);
stack->m_obj
 = v_res_5821_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0___boxed(lean_object* v_sz_5822_, lean_object* v_i_5823_, lean_object* v_bs_5824_){
_start:
{
size_t v_sz_boxed_5825_; size_t v_i_boxed_5826_; lean_object* v_res_5827_; 
v_sz_boxed_5825_ = lean_unbox_usize(v_sz_5822_);
lean_dec(v_sz_5822_);
v_i_boxed_5826_ = lean_unbox_usize(v_i_5823_);
lean_dec(v_i_5823_);
v_res_5827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_boxed_5825_, v_i_boxed_5826_, v_bs_5824_);
return v_res_5827_;
}
}
static lean_object* _init_l_Lake_Check_runComparator___boxed__const__1(void){
_start:
{
uint32_t v___x_5836_; lean_object* v___x_5837_; 
v___x_5836_ = 1;
v___x_5837_ = lean_box_uint32(v___x_5836_);
return v___x_5837_;
}
}
lean_object* l_Lake_Check_runComparator(lean_object* v_configFile_x3f_5838_, lean_object* v_challengeFromExport_x3f_5839_, lean_object* v_solutionFromExport_x3f_5840_, uint8_t v_paranoid_5841_, uint8_t v_inadvisablyNoSandbox_5842_, lean_object* v_lean_5843_, lean_object* v_lake_5844_, lean_object* v_projectDir_5845_){
_start:
{
lean_object* v_a_5848_; lean_object* v___y_5871_; lean_object* v___y_5882_; lean_object* v_a_5883_; lean_object* v___x_5890_; lean_object* v___x_5891_; uint8_t v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; uint8_t v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
v___x_5890_ = ((lean_object*)(l_Lake_Check_runComparator___closed__2));
v___x_5891_ = ((lean_object*)(l_Lake_Check_runComparator___closed__3));
v___x_5892_ = 2;
v___x_5893_ = lean_box(v___x_5892_);
v___x_5894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5894_, 0, v___x_5893_);
lean_ctor_set(v___x_5894_, 1, v_challengeFromExport_x3f_5839_);
v___x_5895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5891_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___x_5896_ = ((lean_object*)(l_Lake_Check_runComparator___closed__4));
v___x_5897_ = 1;
v___x_5898_ = lean_box(v___x_5897_);
v___x_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5898_);
lean_ctor_set(v___x_5899_, 1, v_solutionFromExport_x3f_5840_);
v___x_5900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5896_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v___x_5901_ = lean_unsigned_to_nat(2u);
v___x_5902_ = lean_mk_empty_array_with_capacity(v___x_5901_);
v___x_5903_ = lean_array_push(v___x_5902_, v___x_5895_);
v___x_5904_ = lean_array_push(v___x_5903_, v___x_5900_);
v___x_5905_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_5890_, v___x_5904_);
lean_dec_ref(v___x_5904_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v_a_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_6099_; 
v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_5908_ = v___x_5905_;
v_isShared_5909_ = v_isSharedCheck_6099_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_a_5906_);
lean_dec(v___x_5905_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_6099_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
if (lean_obj_tag(v_a_5906_) == 0)
{
lean_object* v_a_5910_; lean_object* v___x_5912_; 
lean_dec_ref(v_projectDir_5845_);
lean_dec_ref(v_lean_5843_);
v_a_5910_ = lean_ctor_get(v_a_5906_, 0);
lean_inc(v_a_5910_);
lean_dec_ref_known(v_a_5906_, 1);
if (v_isShared_5909_ == 0)
{
lean_ctor_set(v___x_5908_, 0, v_a_5910_);
v___x_5912_ = v___x_5908_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5910_);
v___x_5912_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
return v___x_5912_;
}
}
else
{
lean_object* v_a_5914_; lean_object* v___x_5915_; 
lean_del_object(v___x_5908_);
v_a_5914_ = lean_ctor_get(v_a_5906_, 0);
lean_inc_n(v_a_5914_, 2);
lean_dec_ref_known(v_a_5906_, 1);
v___x_5915_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_5890_, v_paranoid_5841_, v_inadvisablyNoSandbox_5842_, v_lean_5843_, v_lake_5844_, v_projectDir_5845_, v_a_5914_);
if (lean_obj_tag(v___x_5915_) == 0)
{
lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_6090_; 
v_a_5916_ = lean_ctor_get(v___x_5915_, 0);
v_isSharedCheck_6090_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_6090_ == 0)
{
v___x_5918_ = v___x_5915_;
v_isShared_5919_ = v_isSharedCheck_6090_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5915_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_6090_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
if (lean_obj_tag(v_a_5916_) == 0)
{
lean_object* v_a_5920_; lean_object* v___x_5922_; 
lean_dec(v_a_5914_);
v_a_5920_ = lean_ctor_get(v_a_5916_, 0);
lean_inc(v_a_5920_);
lean_dec_ref_known(v_a_5916_, 1);
if (v_isShared_5919_ == 0)
{
lean_ctor_set(v___x_5918_, 0, v_a_5920_);
v___x_5922_ = v___x_5918_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_a_5920_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
else
{
lean_object* v_a_5924_; lean_object* v___y_5926_; lean_object* v___y_5927_; uint8_t v___y_5928_; lean_object* v___y_5929_; lean_object* v___y_5930_; lean_object* v___y_5931_; size_t v___y_5932_; lean_object* v___y_5933_; lean_object* v___y_5978_; lean_object* v___y_5979_; lean_object* v___y_5980_; lean_object* v___y_5981_; lean_object* v___y_5982_; size_t v___y_5983_; lean_object* v___y_5984_; uint8_t v___y_5985_; lean_object* v___y_6006_; lean_object* v___y_6007_; lean_object* v___y_6008_; lean_object* v___y_6009_; lean_object* v___y_6010_; uint8_t v___y_6011_; size_t v___y_6012_; lean_object* v___y_6013_; uint8_t v___y_6014_; lean_object* v___y_6017_; lean_object* v___y_6018_; lean_object* v___y_6019_; lean_object* v___y_6020_; lean_object* v___y_6021_; size_t v___y_6022_; lean_object* v___y_6023_; uint8_t v___y_6024_; lean_object* v___y_6047_; lean_object* v___y_6048_; lean_object* v___y_6049_; lean_object* v___y_6050_; size_t v___y_6051_; lean_object* v___y_6052_; lean_object* v___y_6053_; lean_object* v___y_6064_; 
lean_del_object(v___x_5918_);
v_a_5924_ = lean_ctor_get(v_a_5916_, 0);
lean_inc(v_a_5924_);
lean_dec_ref_known(v_a_5916_, 1);
if (lean_obj_tag(v_configFile_x3f_5838_) == 0)
{
lean_object* v___x_6088_; 
v___x_6088_ = ((lean_object*)(l_Lake_Check_runComparator___closed__7));
v___y_6064_ = v___x_6088_;
goto v___jp_6063_;
}
else
{
lean_object* v_val_6089_; 
v_val_6089_ = lean_ctor_get(v_configFile_x3f_5838_, 0);
v___y_6064_ = v_val_6089_;
goto v___jp_6063_;
}
v___jp_5925_:
{
lean_object* v_projectDir_5934_; lean_object* v_leanPrefix_5935_; lean_object* v_leanPath_5936_; lean_object* v_binPath_5937_; lean_object* v_whichSandbox_5938_; lean_object* v_whichLake_5939_; lean_object* v_lakeHome_5940_; lean_object* v_whichLean4Export_5941_; lean_object* v_whichLeanChecker_5942_; lean_object* v_whichEnvBin_5943_; lean_object* v_bundledKernels_5944_; lean_object* v_moduleStore_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_5970_; 
v_projectDir_5934_ = lean_ctor_get(v_a_5924_, 0);
v_leanPrefix_5935_ = lean_ctor_get(v_a_5924_, 6);
v_leanPath_5936_ = lean_ctor_get(v_a_5924_, 7);
v_binPath_5937_ = lean_ctor_get(v_a_5924_, 8);
v_whichSandbox_5938_ = lean_ctor_get(v_a_5924_, 9);
v_whichLake_5939_ = lean_ctor_get(v_a_5924_, 10);
v_lakeHome_5940_ = lean_ctor_get(v_a_5924_, 11);
v_whichLean4Export_5941_ = lean_ctor_get(v_a_5924_, 12);
v_whichLeanChecker_5942_ = lean_ctor_get(v_a_5924_, 13);
v_whichEnvBin_5943_ = lean_ctor_get(v_a_5924_, 14);
v_bundledKernels_5944_ = lean_ctor_get(v_a_5924_, 16);
v_moduleStore_5945_ = lean_ctor_get(v_a_5924_, 17);
v_isSharedCheck_5970_ = !lean_is_exclusive(v_a_5924_);
if (v_isSharedCheck_5970_ == 0)
{
lean_object* v_unused_5971_; lean_object* v_unused_5972_; lean_object* v_unused_5973_; lean_object* v_unused_5974_; lean_object* v_unused_5975_; lean_object* v_unused_5976_; 
v_unused_5971_ = lean_ctor_get(v_a_5924_, 15);
lean_dec(v_unused_5971_);
v_unused_5972_ = lean_ctor_get(v_a_5924_, 5);
lean_dec(v_unused_5972_);
v_unused_5973_ = lean_ctor_get(v_a_5924_, 4);
lean_dec(v_unused_5973_);
v_unused_5974_ = lean_ctor_get(v_a_5924_, 3);
lean_dec(v_unused_5974_);
v_unused_5975_ = lean_ctor_get(v_a_5924_, 2);
lean_dec(v_unused_5975_);
v_unused_5976_ = lean_ctor_get(v_a_5924_, 1);
lean_dec(v_unused_5976_);
v___x_5947_ = v_a_5924_;
v_isShared_5948_ = v_isSharedCheck_5970_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_moduleStore_5945_);
lean_inc(v_bundledKernels_5944_);
lean_inc(v_whichEnvBin_5943_);
lean_inc(v_whichLeanChecker_5942_);
lean_inc(v_whichLean4Export_5941_);
lean_inc(v_lakeHome_5940_);
lean_inc(v_whichLake_5939_);
lean_inc(v_whichSandbox_5938_);
lean_inc(v_binPath_5937_);
lean_inc(v_leanPath_5936_);
lean_inc(v_leanPrefix_5935_);
lean_inc(v_projectDir_5934_);
lean_dec(v_a_5924_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_5970_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; size_t v_sz_5951_; lean_object* v___x_5952_; lean_object* v___x_5954_; 
v___x_5949_ = l_String_toName(v___y_5927_);
v___x_5950_ = l_String_toName(v___y_5933_);
v_sz_5951_ = lean_array_size(v___y_5929_);
v___x_5952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_5951_, v___y_5932_, v___y_5929_);
lean_inc_ref(v_moduleStore_5945_);
lean_inc_ref(v_bundledKernels_5944_);
lean_inc(v___y_5926_);
lean_inc_ref(v_whichEnvBin_5943_);
lean_inc_ref(v_whichLeanChecker_5942_);
lean_inc_ref(v_whichLean4Export_5941_);
lean_inc_ref(v_lakeHome_5940_);
lean_inc_ref(v_whichLake_5939_);
lean_inc(v_whichSandbox_5938_);
lean_inc_ref(v_leanPrefix_5935_);
lean_inc_ref(v___x_5952_);
lean_inc_ref(v___y_5930_);
lean_inc_ref(v___y_5931_);
lean_inc(v___x_5950_);
lean_inc(v___x_5949_);
lean_inc_ref(v_projectDir_5934_);
if (v_isShared_5948_ == 0)
{
lean_ctor_set(v___x_5947_, 15, v___y_5926_);
lean_ctor_set(v___x_5947_, 5, v___x_5952_);
lean_ctor_set(v___x_5947_, 4, v___y_5930_);
lean_ctor_set(v___x_5947_, 3, v___y_5931_);
lean_ctor_set(v___x_5947_, 2, v___x_5950_);
lean_ctor_set(v___x_5947_, 1, v___x_5949_);
v___x_5954_ = v___x_5947_;
goto v_reusejp_5953_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_projectDir_5934_);
lean_ctor_set(v_reuseFailAlloc_5969_, 1, v___x_5949_);
lean_ctor_set(v_reuseFailAlloc_5969_, 2, v___x_5950_);
lean_ctor_set(v_reuseFailAlloc_5969_, 3, v___y_5931_);
lean_ctor_set(v_reuseFailAlloc_5969_, 4, v___y_5930_);
lean_ctor_set(v_reuseFailAlloc_5969_, 5, v___x_5952_);
lean_ctor_set(v_reuseFailAlloc_5969_, 6, v_leanPrefix_5935_);
lean_ctor_set(v_reuseFailAlloc_5969_, 7, v_leanPath_5936_);
lean_ctor_set(v_reuseFailAlloc_5969_, 8, v_binPath_5937_);
lean_ctor_set(v_reuseFailAlloc_5969_, 9, v_whichSandbox_5938_);
lean_ctor_set(v_reuseFailAlloc_5969_, 10, v_whichLake_5939_);
lean_ctor_set(v_reuseFailAlloc_5969_, 11, v_lakeHome_5940_);
lean_ctor_set(v_reuseFailAlloc_5969_, 12, v_whichLean4Export_5941_);
lean_ctor_set(v_reuseFailAlloc_5969_, 13, v_whichLeanChecker_5942_);
lean_ctor_set(v_reuseFailAlloc_5969_, 14, v_whichEnvBin_5943_);
lean_ctor_set(v_reuseFailAlloc_5969_, 15, v___y_5926_);
lean_ctor_set(v_reuseFailAlloc_5969_, 16, v_bundledKernels_5944_);
lean_ctor_set(v_reuseFailAlloc_5969_, 17, v_moduleStore_5945_);
v___x_5954_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5953_;
}
v_reusejp_5953_:
{
if (v___y_5928_ == 0)
{
lean_object* v___x_5955_; 
lean_dec_ref(v___x_5952_);
lean_dec(v___x_5950_);
lean_dec(v___x_5949_);
lean_dec_ref(v_moduleStore_5945_);
lean_dec_ref(v_bundledKernels_5944_);
lean_dec_ref(v_whichEnvBin_5943_);
lean_dec_ref(v_whichLeanChecker_5942_);
lean_dec_ref(v_whichLean4Export_5941_);
lean_dec_ref(v_lakeHome_5940_);
lean_dec_ref(v_whichLake_5939_);
lean_dec(v_whichSandbox_5938_);
lean_dec_ref(v_leanPrefix_5935_);
lean_dec_ref(v_projectDir_5934_);
lean_dec_ref(v___y_5931_);
lean_dec_ref(v___y_5930_);
lean_dec(v___y_5926_);
v___x_5955_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5954_);
lean_dec_ref(v___x_5954_);
if (lean_obj_tag(v___x_5955_) == 0)
{
lean_object* v_a_5956_; lean_object* v___x_5957_; 
v_a_5956_ = lean_ctor_get(v___x_5955_, 0);
lean_inc(v_a_5956_);
lean_dec_ref_known(v___x_5955_, 1);
v___x_5957_ = l_Lake_Check_runComparator___lam__0(v_a_5956_);
v___y_5871_ = v___x_5957_;
goto v___jp_5870_;
}
else
{
lean_object* v_a_5958_; 
v_a_5958_ = lean_ctor_get(v___x_5955_, 0);
lean_inc(v_a_5958_);
lean_dec_ref_known(v___x_5955_, 1);
v_a_5848_ = v_a_5958_;
goto v___jp_5847_;
}
}
else
{
lean_object* v___x_5959_; 
v___x_5959_ = l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace(v___x_5954_);
lean_dec_ref(v___x_5954_);
if (lean_obj_tag(v___x_5959_) == 0)
{
lean_object* v_a_5960_; lean_object* v_fst_5961_; lean_object* v_snd_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; 
v_a_5960_ = lean_ctor_get(v___x_5959_, 0);
lean_inc(v_a_5960_);
lean_dec_ref_known(v___x_5959_, 1);
v_fst_5961_ = lean_ctor_get(v_a_5960_, 0);
lean_inc(v_fst_5961_);
v_snd_5962_ = lean_ctor_get(v_a_5960_, 1);
lean_inc(v_snd_5962_);
lean_dec(v_a_5960_);
v___x_5963_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v___x_5963_, 0, v_projectDir_5934_);
lean_ctor_set(v___x_5963_, 1, v___x_5949_);
lean_ctor_set(v___x_5963_, 2, v___x_5950_);
lean_ctor_set(v___x_5963_, 3, v___y_5931_);
lean_ctor_set(v___x_5963_, 4, v___y_5930_);
lean_ctor_set(v___x_5963_, 5, v___x_5952_);
lean_ctor_set(v___x_5963_, 6, v_leanPrefix_5935_);
lean_ctor_set(v___x_5963_, 7, v_fst_5961_);
lean_ctor_set(v___x_5963_, 8, v_snd_5962_);
lean_ctor_set(v___x_5963_, 9, v_whichSandbox_5938_);
lean_ctor_set(v___x_5963_, 10, v_whichLake_5939_);
lean_ctor_set(v___x_5963_, 11, v_lakeHome_5940_);
lean_ctor_set(v___x_5963_, 12, v_whichLean4Export_5941_);
lean_ctor_set(v___x_5963_, 13, v_whichLeanChecker_5942_);
lean_ctor_set(v___x_5963_, 14, v_whichEnvBin_5943_);
lean_ctor_set(v___x_5963_, 15, v___y_5926_);
lean_ctor_set(v___x_5963_, 16, v_bundledKernels_5944_);
lean_ctor_set(v___x_5963_, 17, v_moduleStore_5945_);
v___x_5964_ = l___private_Lake_CLI_Check_0__Lake_Check_compareIt(v___x_5963_);
lean_dec_ref_known(v___x_5963_, 18);
if (lean_obj_tag(v___x_5964_) == 0)
{
lean_object* v_a_5965_; lean_object* v___x_5966_; 
v_a_5965_ = lean_ctor_get(v___x_5964_, 0);
lean_inc(v_a_5965_);
lean_dec_ref_known(v___x_5964_, 1);
v___x_5966_ = l_Lake_Check_runComparator___lam__0(v_a_5965_);
v___y_5871_ = v___x_5966_;
goto v___jp_5870_;
}
else
{
lean_object* v_a_5967_; 
v_a_5967_ = lean_ctor_get(v___x_5964_, 0);
lean_inc(v_a_5967_);
lean_dec_ref_known(v___x_5964_, 1);
v_a_5848_ = v_a_5967_;
goto v___jp_5847_;
}
}
else
{
lean_object* v_a_5968_; 
lean_dec_ref(v___x_5952_);
lean_dec(v___x_5950_);
lean_dec(v___x_5949_);
lean_dec_ref(v_moduleStore_5945_);
lean_dec_ref(v_bundledKernels_5944_);
lean_dec_ref(v_whichEnvBin_5943_);
lean_dec_ref(v_whichLeanChecker_5942_);
lean_dec_ref(v_whichLean4Export_5941_);
lean_dec_ref(v_lakeHome_5940_);
lean_dec_ref(v_whichLake_5939_);
lean_dec(v_whichSandbox_5938_);
lean_dec_ref(v_leanPrefix_5935_);
lean_dec_ref(v_projectDir_5934_);
lean_dec_ref(v___y_5931_);
lean_dec_ref(v___y_5930_);
lean_dec(v___y_5926_);
v_a_5968_ = lean_ctor_get(v___x_5959_, 0);
lean_inc(v_a_5968_);
lean_dec_ref_known(v___x_5959_, 1);
v_a_5848_ = v_a_5968_;
goto v___jp_5847_;
}
}
}
}
}
v___jp_5977_:
{
lean_object* v_projectDir_5986_; lean_object* v___x_5987_; 
v_projectDir_5986_ = lean_ctor_get(v_a_5924_, 0);
lean_inc_ref(v_projectDir_5986_);
v___x_5987_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_5890_, v_projectDir_5986_);
if (lean_obj_tag(v___x_5987_) == 0)
{
lean_object* v_a_5988_; lean_object* v___x_5990_; uint8_t v_isShared_5991_; uint8_t v_isSharedCheck_5996_; 
v_a_5988_ = lean_ctor_get(v___x_5987_, 0);
v_isSharedCheck_5996_ = !lean_is_exclusive(v___x_5987_);
if (v_isSharedCheck_5996_ == 0)
{
v___x_5990_ = v___x_5987_;
v_isShared_5991_ = v_isSharedCheck_5996_;
goto v_resetjp_5989_;
}
else
{
lean_inc(v_a_5988_);
lean_dec(v___x_5987_);
v___x_5990_ = lean_box(0);
v_isShared_5991_ = v_isSharedCheck_5996_;
goto v_resetjp_5989_;
}
v_resetjp_5989_:
{
if (lean_obj_tag(v_a_5988_) == 1)
{
lean_object* v_val_5992_; lean_object* v___x_5994_; 
lean_dec_ref(v___y_5984_);
lean_dec_ref(v___y_5982_);
lean_dec_ref(v___y_5981_);
lean_dec_ref(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec(v___y_5978_);
lean_dec(v_a_5924_);
v_val_5992_ = lean_ctor_get(v_a_5988_, 0);
lean_inc(v_val_5992_);
lean_dec_ref_known(v_a_5988_, 1);
if (v_isShared_5991_ == 0)
{
lean_ctor_set(v___x_5990_, 0, v_val_5992_);
v___x_5994_ = v___x_5990_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v_val_5992_);
v___x_5994_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
return v___x_5994_;
}
}
else
{
lean_del_object(v___x_5990_);
lean_dec(v_a_5988_);
v___y_5926_ = v___y_5978_;
v___y_5927_ = v___y_5979_;
v___y_5928_ = v___y_5985_;
v___y_5929_ = v___y_5980_;
v___y_5930_ = v___y_5982_;
v___y_5931_ = v___y_5981_;
v___y_5932_ = v___y_5983_;
v___y_5933_ = v___y_5984_;
goto v___jp_5925_;
}
}
}
else
{
lean_object* v_a_5997_; lean_object* v___x_5999_; uint8_t v_isShared_6000_; uint8_t v_isSharedCheck_6004_; 
lean_dec_ref(v___y_5984_);
lean_dec_ref(v___y_5982_);
lean_dec_ref(v___y_5981_);
lean_dec_ref(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec(v___y_5978_);
lean_dec(v_a_5924_);
v_a_5997_ = lean_ctor_get(v___x_5987_, 0);
v_isSharedCheck_6004_ = !lean_is_exclusive(v___x_5987_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5999_ = v___x_5987_;
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
else
{
lean_inc(v_a_5997_);
lean_dec(v___x_5987_);
v___x_5999_ = lean_box(0);
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
v_resetjp_5998_:
{
lean_object* v___x_6002_; 
if (v_isShared_6000_ == 0)
{
v___x_6002_ = v___x_5999_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_a_5997_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
}
}
}
}
v___jp_6005_:
{
if (v___y_6014_ == 0)
{
uint8_t v___x_6015_; 
v___x_6015_ = 1;
v___y_5978_ = v___y_6006_;
v___y_5979_ = v___y_6007_;
v___y_5980_ = v___y_6008_;
v___y_5981_ = v___y_6010_;
v___y_5982_ = v___y_6009_;
v___y_5983_ = v___y_6012_;
v___y_5984_ = v___y_6013_;
v___y_5985_ = v___x_6015_;
goto v___jp_5977_;
}
else
{
if (v___y_6011_ == 0)
{
v___y_5926_ = v___y_6006_;
v___y_5927_ = v___y_6007_;
v___y_5928_ = v___y_6011_;
v___y_5929_ = v___y_6008_;
v___y_5930_ = v___y_6009_;
v___y_5931_ = v___y_6010_;
v___y_5932_ = v___y_6012_;
v___y_5933_ = v___y_6013_;
goto v___jp_5925_;
}
else
{
v___y_5978_ = v___y_6006_;
v___y_5979_ = v___y_6007_;
v___y_5980_ = v___y_6008_;
v___y_5981_ = v___y_6010_;
v___y_5982_ = v___y_6009_;
v___y_5983_ = v___y_6012_;
v___y_5984_ = v___y_6013_;
v___y_5985_ = v___y_6011_;
goto v___jp_5977_;
}
}
}
v___jp_6016_:
{
lean_object* v___x_6025_; 
v___x_6025_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveExternalKernels(v___y_6017_);
if (lean_obj_tag(v___x_6025_) == 0)
{
lean_object* v_a_6026_; lean_object* v___x_6028_; uint8_t v_isShared_6029_; uint8_t v_isSharedCheck_6037_; 
v_a_6026_ = lean_ctor_get(v___x_6025_, 0);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_6025_);
if (v_isSharedCheck_6037_ == 0)
{
v___x_6028_ = v___x_6025_;
v_isShared_6029_ = v_isSharedCheck_6037_;
goto v_resetjp_6027_;
}
else
{
lean_inc(v_a_6026_);
lean_dec(v___x_6025_);
v___x_6028_ = lean_box(0);
v_isShared_6029_ = v_isSharedCheck_6037_;
goto v_resetjp_6027_;
}
v_resetjp_6027_:
{
if (lean_obj_tag(v_a_6026_) == 0)
{
lean_object* v_a_6030_; lean_object* v___x_6032_; 
lean_dec_ref(v___y_6023_);
lean_dec_ref(v___y_6021_);
lean_dec_ref(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec_ref(v___y_6018_);
lean_dec(v_a_5924_);
lean_dec(v_a_5914_);
v_a_6030_ = lean_ctor_get(v_a_6026_, 0);
lean_inc(v_a_6030_);
lean_dec_ref_known(v_a_6026_, 1);
if (v_isShared_6029_ == 0)
{
lean_ctor_set(v___x_6028_, 0, v_a_6030_);
v___x_6032_ = v___x_6028_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_a_6030_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
else
{
lean_object* v_a_6034_; uint8_t v___x_6035_; 
lean_del_object(v___x_6028_);
v_a_6034_ = lean_ctor_get(v_a_6026_, 0);
lean_inc(v_a_6034_);
lean_dec_ref_known(v_a_6026_, 1);
v___x_6035_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5914_, v___x_5892_);
if (v___x_6035_ == 0)
{
lean_dec(v_a_5914_);
v___y_6006_ = v_a_6034_;
v___y_6007_ = v___y_6018_;
v___y_6008_ = v___y_6019_;
v___y_6009_ = v___y_6020_;
v___y_6010_ = v___y_6021_;
v___y_6011_ = v___y_6024_;
v___y_6012_ = v___y_6022_;
v___y_6013_ = v___y_6023_;
v___y_6014_ = v___x_6035_;
goto v___jp_6005_;
}
else
{
uint8_t v___x_6036_; 
v___x_6036_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_5914_, v___x_5897_);
lean_dec(v_a_5914_);
v___y_6006_ = v_a_6034_;
v___y_6007_ = v___y_6018_;
v___y_6008_ = v___y_6019_;
v___y_6009_ = v___y_6020_;
v___y_6010_ = v___y_6021_;
v___y_6011_ = v___y_6024_;
v___y_6012_ = v___y_6022_;
v___y_6013_ = v___y_6023_;
v___y_6014_ = v___x_6036_;
goto v___jp_6005_;
}
}
}
}
else
{
lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6045_; 
lean_dec_ref(v___y_6023_);
lean_dec_ref(v___y_6021_);
lean_dec_ref(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec_ref(v___y_6018_);
lean_dec(v_a_5924_);
lean_dec(v_a_5914_);
v_a_6038_ = lean_ctor_get(v___x_6025_, 0);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_6025_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6040_ = v___x_6025_;
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_6025_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
lean_object* v___x_6043_; 
if (v_isShared_6041_ == 0)
{
v___x_6043_ = v___x_6040_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_a_6038_);
v___x_6043_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
return v___x_6043_;
}
}
}
}
v___jp_6046_:
{
size_t v_sz_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; uint8_t v___x_6058_; 
v_sz_6054_ = lean_array_size(v___y_6053_);
v___x_6055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_6054_, v___y_6051_, v___y_6053_);
v___x_6056_ = lean_array_get_size(v___y_6050_);
v___x_6057_ = lean_unsigned_to_nat(0u);
v___x_6058_ = lean_nat_dec_eq(v___x_6056_, v___x_6057_);
if (v___x_6058_ == 0)
{
v___y_6017_ = v___y_6047_;
v___y_6018_ = v___y_6048_;
v___y_6019_ = v___y_6049_;
v___y_6020_ = v___x_6055_;
v___y_6021_ = v___y_6050_;
v___y_6022_ = v___y_6051_;
v___y_6023_ = v___y_6052_;
v___y_6024_ = v___x_6058_;
goto v___jp_6016_;
}
else
{
lean_object* v___x_6059_; uint8_t v___x_6060_; 
v___x_6059_ = lean_array_get_size(v___x_6055_);
v___x_6060_ = lean_nat_dec_eq(v___x_6059_, v___x_6057_);
if (v___x_6060_ == 0)
{
v___y_6017_ = v___y_6047_;
v___y_6018_ = v___y_6048_;
v___y_6019_ = v___y_6049_;
v___y_6020_ = v___x_6055_;
v___y_6021_ = v___y_6050_;
v___y_6022_ = v___y_6051_;
v___y_6023_ = v___y_6052_;
v___y_6024_ = v___x_6060_;
goto v___jp_6016_;
}
else
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
lean_dec_ref(v___x_6055_);
lean_dec_ref(v___y_6052_);
lean_dec_ref(v___y_6050_);
lean_dec_ref(v___y_6049_);
lean_dec_ref(v___y_6048_);
lean_dec_ref(v___y_6047_);
lean_dec(v_a_5924_);
lean_dec(v_a_5914_);
v___x_6061_ = ((lean_object*)(l_Lake_Check_runComparator___closed__5));
v___x_6062_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_6061_);
return v___x_6062_;
}
}
}
v___jp_6063_:
{
lean_object* v___x_6065_; 
v___x_6065_ = l_IO_FS_readFile(v___y_6064_);
if (lean_obj_tag(v___x_6065_) == 0)
{
lean_object* v_a_6066_; lean_object* v___x_6067_; 
v_a_6066_ = lean_ctor_get(v___x_6065_, 0);
lean_inc(v_a_6066_);
lean_dec_ref_known(v___x_6065_, 1);
v___x_6067_ = l_Lean_Json_parse(v_a_6066_);
if (lean_obj_tag(v___x_6067_) == 0)
{
lean_object* v_a_6068_; 
lean_dec(v_a_5924_);
lean_dec(v_a_5914_);
v_a_6068_ = lean_ctor_get(v___x_6067_, 0);
lean_inc(v_a_6068_);
lean_dec_ref_known(v___x_6067_, 1);
v___y_5882_ = v___y_6064_;
v_a_5883_ = v_a_6068_;
goto v___jp_5881_;
}
else
{
lean_object* v_a_6069_; lean_object* v___x_6070_; 
v_a_6069_ = lean_ctor_get(v___x_6067_, 0);
lean_inc(v_a_6069_);
lean_dec_ref_known(v___x_6067_, 1);
v___x_6070_ = l_Lake_Check_instFromJsonConfig_fromJson(v_a_6069_);
if (lean_obj_tag(v___x_6070_) == 0)
{
lean_object* v_a_6071_; 
lean_dec(v_a_5924_);
lean_dec(v_a_5914_);
v_a_6071_ = lean_ctor_get(v___x_6070_, 0);
lean_inc(v_a_6071_);
lean_dec_ref_known(v___x_6070_, 1);
v___y_5882_ = v___y_6064_;
v_a_5883_ = v_a_6071_;
goto v___jp_5881_;
}
else
{
lean_object* v_a_6072_; lean_object* v_challenge__module_6073_; lean_object* v_solution__module_6074_; lean_object* v_theorem__names_6075_; lean_object* v_definition__names_6076_; lean_object* v_permitted__axioms_6077_; size_t v_sz_6078_; size_t v___x_6079_; lean_object* v___x_6080_; 
v_a_6072_ = lean_ctor_get(v___x_6070_, 0);
lean_inc(v_a_6072_);
lean_dec_ref_known(v___x_6070_, 1);
v_challenge__module_6073_ = lean_ctor_get(v_a_6072_, 0);
lean_inc_ref(v_challenge__module_6073_);
v_solution__module_6074_ = lean_ctor_get(v_a_6072_, 1);
lean_inc_ref(v_solution__module_6074_);
v_theorem__names_6075_ = lean_ctor_get(v_a_6072_, 2);
v_definition__names_6076_ = lean_ctor_get(v_a_6072_, 3);
v_permitted__axioms_6077_ = lean_ctor_get(v_a_6072_, 4);
lean_inc_ref(v_permitted__axioms_6077_);
v_sz_6078_ = lean_array_size(v_theorem__names_6075_);
v___x_6079_ = ((size_t)0ULL);
lean_inc_ref(v_theorem__names_6075_);
v___x_6080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Check_runComparator_spec__0(v_sz_6078_, v___x_6079_, v_theorem__names_6075_);
if (lean_obj_tag(v_definition__names_6076_) == 0)
{
lean_object* v___x_6081_; 
v___x_6081_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_safeResolveWorkspace___closed__13));
v___y_6047_ = v_a_6072_;
v___y_6048_ = v_challenge__module_6073_;
v___y_6049_ = v_permitted__axioms_6077_;
v___y_6050_ = v___x_6080_;
v___y_6051_ = v___x_6079_;
v___y_6052_ = v_solution__module_6074_;
v___y_6053_ = v___x_6081_;
goto v___jp_6046_;
}
else
{
lean_object* v_val_6082_; 
v_val_6082_ = lean_ctor_get(v_definition__names_6076_, 0);
lean_inc(v_val_6082_);
v___y_6047_ = v_a_6072_;
v___y_6048_ = v_challenge__module_6073_;
v___y_6049_ = v_permitted__axioms_6077_;
v___y_6050_ = v___x_6080_;
v___y_6051_ = v___x_6079_;
v___y_6052_ = v_solution__module_6074_;
v___y_6053_ = v_val_6082_;
goto v___jp_6046_;
}
}
}
}
else
{
lean_object* v_a_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; 
lean_dec(v_a_5924_);
lean_dec(v_a_5914_);
v_a_6083_ = lean_ctor_get(v___x_6065_, 0);
lean_inc(v_a_6083_);
lean_dec_ref_known(v___x_6065_, 1);
v___x_6084_ = ((lean_object*)(l_Lake_Check_runComparator___closed__6));
v___x_6085_ = lean_io_error_to_string(v_a_6083_);
v___x_6086_ = lean_string_append(v___x_6084_, v___x_6085_);
lean_dec_ref(v___x_6085_);
v___x_6087_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_6086_);
lean_dec_ref(v___x_6086_);
return v___x_6087_;
}
}
}
}
}
else
{
lean_object* v_a_6091_; lean_object* v___x_6093_; uint8_t v_isShared_6094_; uint8_t v_isSharedCheck_6098_; 
lean_dec(v_a_5914_);
v_a_6091_ = lean_ctor_get(v___x_5915_, 0);
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_6098_ == 0)
{
v___x_6093_ = v___x_5915_;
v_isShared_6094_ = v_isSharedCheck_6098_;
goto v_resetjp_6092_;
}
else
{
lean_inc(v_a_6091_);
lean_dec(v___x_5915_);
v___x_6093_ = lean_box(0);
v_isShared_6094_ = v_isSharedCheck_6098_;
goto v_resetjp_6092_;
}
v_resetjp_6092_:
{
lean_object* v___x_6096_; 
if (v_isShared_6094_ == 0)
{
v___x_6096_ = v___x_6093_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_a_6091_);
v___x_6096_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
return v___x_6096_;
}
}
}
}
}
}
else
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6107_; 
lean_dec_ref(v_projectDir_5845_);
lean_dec_ref(v_lean_5843_);
v_a_6100_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_6107_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6102_ = v___x_5905_;
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_5905_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6107_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v___x_6105_; 
if (v_isShared_6103_ == 0)
{
v___x_6105_ = v___x_6102_;
goto v_reusejp_6104_;
}
else
{
lean_object* v_reuseFailAlloc_6106_; 
v_reuseFailAlloc_6106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6100_);
v___x_6105_ = v_reuseFailAlloc_6106_;
goto v_reusejp_6104_;
}
v_reusejp_6104_:
{
return v___x_6105_;
}
}
}
v___jp_5847_:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5849_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_5850_ = lean_io_error_to_string(v_a_5848_);
v___x_5851_ = lean_string_append(v___x_5849_, v___x_5850_);
lean_dec_ref(v___x_5850_);
v___x_5852_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_5851_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5860_; 
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5860_ == 0)
{
lean_object* v_unused_5861_; 
v_unused_5861_ = lean_ctor_get(v___x_5852_, 0);
lean_dec(v_unused_5861_);
v___x_5854_ = v___x_5852_;
v_isShared_5855_ = v_isSharedCheck_5860_;
goto v_resetjp_5853_;
}
else
{
lean_dec(v___x_5852_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5860_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v___x_5856_; lean_object* v___x_5858_; 
v___x_5856_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_5855_ == 0)
{
lean_ctor_set(v___x_5854_, 0, v___x_5856_);
v___x_5858_ = v___x_5854_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v___x_5856_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
}
else
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
v_a_5862_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5852_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5852_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5865_ == 0)
{
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_a_5862_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
}
v___jp_5870_:
{
lean_object* v_a_5872_; lean_object* v___x_5874_; uint8_t v_isShared_5875_; uint8_t v_isSharedCheck_5880_; 
v_a_5872_ = lean_ctor_get(v___y_5871_, 0);
v_isSharedCheck_5880_ = !lean_is_exclusive(v___y_5871_);
if (v_isSharedCheck_5880_ == 0)
{
v___x_5874_ = v___y_5871_;
v_isShared_5875_ = v_isSharedCheck_5880_;
goto v_resetjp_5873_;
}
else
{
lean_inc(v_a_5872_);
lean_dec(v___y_5871_);
v___x_5874_ = lean_box(0);
v_isShared_5875_ = v_isSharedCheck_5880_;
goto v_resetjp_5873_;
}
v_resetjp_5873_:
{
lean_object* v_a_5876_; lean_object* v___x_5878_; 
v_a_5876_ = lean_ctor_get(v_a_5872_, 0);
lean_inc(v_a_5876_);
lean_dec(v_a_5872_);
if (v_isShared_5875_ == 0)
{
lean_ctor_set(v___x_5874_, 0, v_a_5876_);
v___x_5878_ = v___x_5874_;
goto v_reusejp_5877_;
}
else
{
lean_object* v_reuseFailAlloc_5879_; 
v_reuseFailAlloc_5879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5879_, 0, v_a_5876_);
v___x_5878_ = v_reuseFailAlloc_5879_;
goto v_reusejp_5877_;
}
v_reusejp_5877_:
{
return v___x_5878_;
}
}
}
v___jp_5881_:
{
lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; 
v___x_5884_ = ((lean_object*)(l_Lake_Check_runComparator___closed__0));
v___x_5885_ = lean_string_append(v___x_5884_, v___y_5882_);
v___x_5886_ = ((lean_object*)(l_Lake_Check_runComparator___closed__1));
v___x_5887_ = lean_string_append(v___x_5885_, v___x_5886_);
v___x_5888_ = lean_string_append(v___x_5887_, v_a_5883_);
lean_dec_ref(v_a_5883_);
v___x_5889_ = l___private_Lake_CLI_Check_0__Lake_Check_cannotRun(v___x_5888_);
lean_dec_ref(v___x_5888_);
return v___x_5889_;
}
}
}
LEAN_EXPORT void l_Lake_Check_runComparator_0interp(lean_interpreter_value* stack)
{
lean_object* v_configFile_x3f_5838_ = stack[0].m_obj;
lean_object* v_challengeFromExport_x3f_5839_ = stack[1].m_obj;
lean_object* v_solutionFromExport_x3f_5840_ = stack[2].m_obj;
uint8_t v_paranoid_5841_ = stack[3].m_num;
uint8_t v_inadvisablyNoSandbox_5842_ = stack[4].m_num;
lean_object* v_lean_5843_ = stack[5].m_obj;
lean_object* v_lake_5844_ = stack[6].m_obj;
lean_object* v_projectDir_5845_ = stack[7].m_obj;
lean_object* v_res_6108_;
v_res_6108_ = l_Lake_Check_runComparator(v_configFile_x3f_5838_, v_challengeFromExport_x3f_5839_, v_solutionFromExport_x3f_5840_, v_paranoid_5841_, v_inadvisablyNoSandbox_5842_, v_lean_5843_, v_lake_5844_, v_projectDir_5845_);
stack->m_obj
 = v_res_6108_;
}
LEAN_EXPORT lean_object* l_Lake_Check_runComparator___boxed(lean_object* v_configFile_x3f_6109_, lean_object* v_challengeFromExport_x3f_6110_, lean_object* v_solutionFromExport_x3f_6111_, lean_object* v_paranoid_6112_, lean_object* v_inadvisablyNoSandbox_6113_, lean_object* v_lean_6114_, lean_object* v_lake_6115_, lean_object* v_projectDir_6116_, lean_object* v_a_6117_){
_start:
{
uint8_t v_paranoid_boxed_6118_; uint8_t v_inadvisablyNoSandbox_boxed_6119_; lean_object* v_res_6120_; 
v_paranoid_boxed_6118_ = lean_unbox(v_paranoid_6112_);
v_inadvisablyNoSandbox_boxed_6119_ = lean_unbox(v_inadvisablyNoSandbox_6113_);
v_res_6120_ = l_Lake_Check_runComparator(v_configFile_x3f_6109_, v_challengeFromExport_x3f_6110_, v_solutionFromExport_x3f_6111_, v_paranoid_boxed_6118_, v_inadvisablyNoSandbox_boxed_6119_, v_lean_6114_, v_lake_6115_, v_projectDir_6116_);
lean_dec_ref(v_lake_6115_);
lean_dec(v_configFile_x3f_6109_);
return v_res_6120_;
}
}
lean_object* l_Lake_Check_runCheck(lean_object* v_fromExport_x3f_6121_, uint8_t v_paranoid_6122_, uint8_t v_inadvisablyNoSandbox_6123_, lean_object* v_lean_6124_, lean_object* v_lake_6125_, lean_object* v_projectDir_6126_){
_start:
{
lean_object* v___x_6128_; lean_object* v___x_6129_; uint8_t v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; 
v___x_6128_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_withSafeCheckExport___redArg___lam__0___closed__0));
v___x_6129_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_runBuiltinKernel___closed__1));
v___x_6130_ = 0;
v___x_6131_ = lean_box(v___x_6130_);
v___x_6132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
lean_ctor_set(v___x_6132_, 1, v_fromExport_x3f_6121_);
v___x_6133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6133_, 0, v___x_6129_);
lean_ctor_set(v___x_6133_, 1, v___x_6132_);
v___x_6134_ = lean_unsigned_to_nat(1u);
v___x_6135_ = lean_mk_empty_array_with_capacity(v___x_6134_);
v___x_6136_ = lean_array_push(v___x_6135_, v___x_6133_);
v___x_6137_ = l___private_Lake_CLI_Check_0__Lake_Check_resolveModuleStore(v___x_6128_, v___x_6136_);
lean_dec_ref(v___x_6136_);
if (lean_obj_tag(v___x_6137_) == 0)
{
lean_object* v_a_6138_; lean_object* v___x_6140_; uint8_t v_isShared_6141_; uint8_t v_isSharedCheck_6247_; 
v_a_6138_ = lean_ctor_get(v___x_6137_, 0);
v_isSharedCheck_6247_ = !lean_is_exclusive(v___x_6137_);
if (v_isSharedCheck_6247_ == 0)
{
v___x_6140_ = v___x_6137_;
v_isShared_6141_ = v_isSharedCheck_6247_;
goto v_resetjp_6139_;
}
else
{
lean_inc(v_a_6138_);
lean_dec(v___x_6137_);
v___x_6140_ = lean_box(0);
v_isShared_6141_ = v_isSharedCheck_6247_;
goto v_resetjp_6139_;
}
v_resetjp_6139_:
{
if (lean_obj_tag(v_a_6138_) == 0)
{
lean_object* v_a_6142_; lean_object* v___x_6144_; 
lean_dec_ref(v_projectDir_6126_);
lean_dec_ref(v_lean_6124_);
v_a_6142_ = lean_ctor_get(v_a_6138_, 0);
lean_inc(v_a_6142_);
lean_dec_ref_known(v_a_6138_, 1);
if (v_isShared_6141_ == 0)
{
lean_ctor_set(v___x_6140_, 0, v_a_6142_);
v___x_6144_ = v___x_6140_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_a_6142_);
v___x_6144_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
return v___x_6144_;
}
}
else
{
lean_object* v_a_6146_; lean_object* v___x_6147_; 
lean_del_object(v___x_6140_);
v_a_6146_ = lean_ctor_get(v_a_6138_, 0);
lean_inc_n(v_a_6146_, 2);
lean_dec_ref_known(v_a_6138_, 1);
v___x_6147_ = l___private_Lake_CLI_Check_0__Lake_Check_mkContext(v___x_6128_, v_paranoid_6122_, v_inadvisablyNoSandbox_6123_, v_lean_6124_, v_lake_6125_, v_projectDir_6126_, v_a_6146_);
if (lean_obj_tag(v___x_6147_) == 0)
{
lean_object* v_a_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6238_; 
v_a_6148_ = lean_ctor_get(v___x_6147_, 0);
v_isSharedCheck_6238_ = !lean_is_exclusive(v___x_6147_);
if (v_isSharedCheck_6238_ == 0)
{
v___x_6150_ = v___x_6147_;
v_isShared_6151_ = v_isSharedCheck_6238_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_a_6148_);
lean_dec(v___x_6147_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6238_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
if (lean_obj_tag(v_a_6148_) == 0)
{
lean_object* v_a_6152_; lean_object* v___x_6154_; 
lean_dec(v_a_6146_);
v_a_6152_ = lean_ctor_get(v_a_6148_, 0);
lean_inc(v_a_6152_);
lean_dec_ref_known(v_a_6148_, 1);
if (v_isShared_6151_ == 0)
{
lean_ctor_set(v___x_6150_, 0, v_a_6152_);
v___x_6154_ = v___x_6150_;
goto v_reusejp_6153_;
}
else
{
lean_object* v_reuseFailAlloc_6155_; 
v_reuseFailAlloc_6155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6155_, 0, v_a_6152_);
v___x_6154_ = v_reuseFailAlloc_6155_;
goto v_reusejp_6153_;
}
v_reusejp_6153_:
{
return v___x_6154_;
}
}
else
{
lean_object* v_a_6156_; uint8_t v___x_6218_; 
lean_del_object(v___x_6150_);
v_a_6156_ = lean_ctor_get(v_a_6148_, 0);
lean_inc(v_a_6156_);
lean_dec_ref_known(v_a_6148_, 1);
v___x_6218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Check_0__Lake_Check_checkProject_spec__0___redArg(v_a_6146_, v___x_6130_);
lean_dec(v_a_6146_);
if (v___x_6218_ == 0)
{
lean_object* v_projectDir_6219_; lean_object* v___x_6220_; 
v_projectDir_6219_ = lean_ctor_get(v_a_6156_, 0);
lean_inc_ref(v_projectDir_6219_);
v___x_6220_ = l___private_Lake_CLI_Check_0__Lake_Check_checkManifest(v___x_6128_, v_projectDir_6219_);
if (lean_obj_tag(v___x_6220_) == 0)
{
lean_object* v_a_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6229_; 
v_a_6221_ = lean_ctor_get(v___x_6220_, 0);
v_isSharedCheck_6229_ = !lean_is_exclusive(v___x_6220_);
if (v_isSharedCheck_6229_ == 0)
{
v___x_6223_ = v___x_6220_;
v_isShared_6224_ = v_isSharedCheck_6229_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_a_6221_);
lean_dec(v___x_6220_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6229_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
if (lean_obj_tag(v_a_6221_) == 1)
{
lean_object* v_val_6225_; lean_object* v___x_6227_; 
lean_dec(v_a_6156_);
v_val_6225_ = lean_ctor_get(v_a_6221_, 0);
lean_inc(v_val_6225_);
lean_dec_ref_known(v_a_6221_, 1);
if (v_isShared_6224_ == 0)
{
lean_ctor_set(v___x_6223_, 0, v_val_6225_);
v___x_6227_ = v___x_6223_;
goto v_reusejp_6226_;
}
else
{
lean_object* v_reuseFailAlloc_6228_; 
v_reuseFailAlloc_6228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_val_6225_);
v___x_6227_ = v_reuseFailAlloc_6228_;
goto v_reusejp_6226_;
}
v_reusejp_6226_:
{
return v___x_6227_;
}
}
else
{
lean_del_object(v___x_6223_);
lean_dec(v_a_6221_);
goto v___jp_6157_;
}
}
}
else
{
lean_object* v_a_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6237_; 
lean_dec(v_a_6156_);
v_a_6230_ = lean_ctor_get(v___x_6220_, 0);
v_isSharedCheck_6237_ = !lean_is_exclusive(v___x_6220_);
if (v_isSharedCheck_6237_ == 0)
{
v___x_6232_ = v___x_6220_;
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
else
{
lean_inc(v_a_6230_);
lean_dec(v___x_6220_);
v___x_6232_ = lean_box(0);
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
v_resetjp_6231_:
{
lean_object* v___x_6235_; 
if (v_isShared_6233_ == 0)
{
v___x_6235_ = v___x_6232_;
goto v_reusejp_6234_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_a_6230_);
v___x_6235_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6234_;
}
v_reusejp_6234_:
{
return v___x_6235_;
}
}
}
}
else
{
goto v___jp_6157_;
}
v___jp_6157_:
{
lean_object* v_projectDir_6158_; lean_object* v_theoremNames_6159_; lean_object* v_definitionNames_6160_; lean_object* v_leanPrefix_6161_; lean_object* v_leanPath_6162_; lean_object* v_binPath_6163_; lean_object* v_whichSandbox_6164_; lean_object* v_whichLake_6165_; lean_object* v_lakeHome_6166_; lean_object* v_whichLean4Export_6167_; lean_object* v_whichLeanChecker_6168_; lean_object* v_whichEnvBin_6169_; lean_object* v_bundledKernels_6170_; lean_object* v_moduleStore_6171_; lean_object* v___x_6173_; uint8_t v_isShared_6174_; uint8_t v_isSharedCheck_6213_; 
v_projectDir_6158_ = lean_ctor_get(v_a_6156_, 0);
v_theoremNames_6159_ = lean_ctor_get(v_a_6156_, 3);
v_definitionNames_6160_ = lean_ctor_get(v_a_6156_, 4);
v_leanPrefix_6161_ = lean_ctor_get(v_a_6156_, 6);
v_leanPath_6162_ = lean_ctor_get(v_a_6156_, 7);
v_binPath_6163_ = lean_ctor_get(v_a_6156_, 8);
v_whichSandbox_6164_ = lean_ctor_get(v_a_6156_, 9);
v_whichLake_6165_ = lean_ctor_get(v_a_6156_, 10);
v_lakeHome_6166_ = lean_ctor_get(v_a_6156_, 11);
v_whichLean4Export_6167_ = lean_ctor_get(v_a_6156_, 12);
v_whichLeanChecker_6168_ = lean_ctor_get(v_a_6156_, 13);
v_whichEnvBin_6169_ = lean_ctor_get(v_a_6156_, 14);
v_bundledKernels_6170_ = lean_ctor_get(v_a_6156_, 16);
v_moduleStore_6171_ = lean_ctor_get(v_a_6156_, 17);
v_isSharedCheck_6213_ = !lean_is_exclusive(v_a_6156_);
if (v_isSharedCheck_6213_ == 0)
{
lean_object* v_unused_6214_; lean_object* v_unused_6215_; lean_object* v_unused_6216_; lean_object* v_unused_6217_; 
v_unused_6214_ = lean_ctor_get(v_a_6156_, 15);
lean_dec(v_unused_6214_);
v_unused_6215_ = lean_ctor_get(v_a_6156_, 5);
lean_dec(v_unused_6215_);
v_unused_6216_ = lean_ctor_get(v_a_6156_, 2);
lean_dec(v_unused_6216_);
v_unused_6217_ = lean_ctor_get(v_a_6156_, 1);
lean_dec(v_unused_6217_);
v___x_6173_ = v_a_6156_;
v_isShared_6174_ = v_isSharedCheck_6213_;
goto v_resetjp_6172_;
}
else
{
lean_inc(v_moduleStore_6171_);
lean_inc(v_bundledKernels_6170_);
lean_inc(v_whichEnvBin_6169_);
lean_inc(v_whichLeanChecker_6168_);
lean_inc(v_whichLean4Export_6167_);
lean_inc(v_lakeHome_6166_);
lean_inc(v_whichLake_6165_);
lean_inc(v_whichSandbox_6164_);
lean_inc(v_binPath_6163_);
lean_inc(v_leanPath_6162_);
lean_inc(v_leanPrefix_6161_);
lean_inc(v_definitionNames_6160_);
lean_inc(v_theoremNames_6159_);
lean_inc(v_projectDir_6158_);
lean_dec(v_a_6156_);
v___x_6173_ = lean_box(0);
v_isShared_6174_ = v_isSharedCheck_6213_;
goto v_resetjp_6172_;
}
v_resetjp_6172_:
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6179_; 
v___x_6175_ = lean_box(1);
v___x_6176_ = lean_box(0);
v___x_6177_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_standardAxioms));
if (v_isShared_6174_ == 0)
{
lean_ctor_set(v___x_6173_, 15, v___x_6175_);
lean_ctor_set(v___x_6173_, 5, v___x_6177_);
lean_ctor_set(v___x_6173_, 2, v___x_6176_);
lean_ctor_set(v___x_6173_, 1, v___x_6176_);
v___x_6179_ = v___x_6173_;
goto v_reusejp_6178_;
}
else
{
lean_object* v_reuseFailAlloc_6212_; 
v_reuseFailAlloc_6212_ = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(v_reuseFailAlloc_6212_, 0, v_projectDir_6158_);
lean_ctor_set(v_reuseFailAlloc_6212_, 1, v___x_6176_);
lean_ctor_set(v_reuseFailAlloc_6212_, 2, v___x_6176_);
lean_ctor_set(v_reuseFailAlloc_6212_, 3, v_theoremNames_6159_);
lean_ctor_set(v_reuseFailAlloc_6212_, 4, v_definitionNames_6160_);
lean_ctor_set(v_reuseFailAlloc_6212_, 5, v___x_6177_);
lean_ctor_set(v_reuseFailAlloc_6212_, 6, v_leanPrefix_6161_);
lean_ctor_set(v_reuseFailAlloc_6212_, 7, v_leanPath_6162_);
lean_ctor_set(v_reuseFailAlloc_6212_, 8, v_binPath_6163_);
lean_ctor_set(v_reuseFailAlloc_6212_, 9, v_whichSandbox_6164_);
lean_ctor_set(v_reuseFailAlloc_6212_, 10, v_whichLake_6165_);
lean_ctor_set(v_reuseFailAlloc_6212_, 11, v_lakeHome_6166_);
lean_ctor_set(v_reuseFailAlloc_6212_, 12, v_whichLean4Export_6167_);
lean_ctor_set(v_reuseFailAlloc_6212_, 13, v_whichLeanChecker_6168_);
lean_ctor_set(v_reuseFailAlloc_6212_, 14, v_whichEnvBin_6169_);
lean_ctor_set(v_reuseFailAlloc_6212_, 15, v___x_6175_);
lean_ctor_set(v_reuseFailAlloc_6212_, 16, v_bundledKernels_6170_);
lean_ctor_set(v_reuseFailAlloc_6212_, 17, v_moduleStore_6171_);
v___x_6179_ = v_reuseFailAlloc_6212_;
goto v_reusejp_6178_;
}
v_reusejp_6178_:
{
lean_object* v___x_6180_; 
v___x_6180_ = l___private_Lake_CLI_Check_0__Lake_Check_checkProject(v___x_6179_);
lean_dec_ref(v___x_6179_);
if (lean_obj_tag(v___x_6180_) == 0)
{
lean_object* v___x_6182_; uint8_t v_isShared_6183_; uint8_t v_isSharedCheck_6188_; 
v_isSharedCheck_6188_ = !lean_is_exclusive(v___x_6180_);
if (v_isSharedCheck_6188_ == 0)
{
lean_object* v_unused_6189_; 
v_unused_6189_ = lean_ctor_get(v___x_6180_, 0);
lean_dec(v_unused_6189_);
v___x_6182_ = v___x_6180_;
v_isShared_6183_ = v_isSharedCheck_6188_;
goto v_resetjp_6181_;
}
else
{
lean_dec(v___x_6180_);
v___x_6182_ = lean_box(0);
v_isShared_6183_ = v_isSharedCheck_6188_;
goto v_resetjp_6181_;
}
v_resetjp_6181_:
{
lean_object* v___x_6184_; lean_object* v___x_6186_; 
v___x_6184_ = l_Lake_Check_runComparator___lam__0___closed__0___boxed__const__1;
if (v_isShared_6183_ == 0)
{
lean_ctor_set(v___x_6182_, 0, v___x_6184_);
v___x_6186_ = v___x_6182_;
goto v_reusejp_6185_;
}
else
{
lean_object* v_reuseFailAlloc_6187_; 
v_reuseFailAlloc_6187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6187_, 0, v___x_6184_);
v___x_6186_ = v_reuseFailAlloc_6187_;
goto v_reusejp_6185_;
}
v_reusejp_6185_:
{
return v___x_6186_;
}
}
}
else
{
lean_object* v_a_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; 
v_a_6190_ = lean_ctor_get(v___x_6180_, 0);
lean_inc(v_a_6190_);
lean_dec_ref_known(v___x_6180_, 1);
v___x_6191_ = ((lean_object*)(l___private_Lake_CLI_Check_0__Lake_Check_cannotRun___closed__0));
v___x_6192_ = lean_io_error_to_string(v_a_6190_);
v___x_6193_ = lean_string_append(v___x_6191_, v___x_6192_);
lean_dec_ref(v___x_6192_);
v___x_6194_ = l_IO_eprintln___at___00__private_Lake_CLI_Check_0__Lake_Check_cannotRun_spec__0(v___x_6193_);
if (lean_obj_tag(v___x_6194_) == 0)
{
lean_object* v___x_6196_; uint8_t v_isShared_6197_; uint8_t v_isSharedCheck_6202_; 
v_isSharedCheck_6202_ = !lean_is_exclusive(v___x_6194_);
if (v_isSharedCheck_6202_ == 0)
{
lean_object* v_unused_6203_; 
v_unused_6203_ = lean_ctor_get(v___x_6194_, 0);
lean_dec(v_unused_6203_);
v___x_6196_ = v___x_6194_;
v_isShared_6197_ = v_isSharedCheck_6202_;
goto v_resetjp_6195_;
}
else
{
lean_dec(v___x_6194_);
v___x_6196_ = lean_box(0);
v_isShared_6197_ = v_isSharedCheck_6202_;
goto v_resetjp_6195_;
}
v_resetjp_6195_:
{
lean_object* v___x_6198_; lean_object* v___x_6200_; 
v___x_6198_ = l_Lake_Check_runComparator___boxed__const__1;
if (v_isShared_6197_ == 0)
{
lean_ctor_set(v___x_6196_, 0, v___x_6198_);
v___x_6200_ = v___x_6196_;
goto v_reusejp_6199_;
}
else
{
lean_object* v_reuseFailAlloc_6201_; 
v_reuseFailAlloc_6201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6201_, 0, v___x_6198_);
v___x_6200_ = v_reuseFailAlloc_6201_;
goto v_reusejp_6199_;
}
v_reusejp_6199_:
{
return v___x_6200_;
}
}
}
else
{
lean_object* v_a_6204_; lean_object* v___x_6206_; uint8_t v_isShared_6207_; uint8_t v_isSharedCheck_6211_; 
v_a_6204_ = lean_ctor_get(v___x_6194_, 0);
v_isSharedCheck_6211_ = !lean_is_exclusive(v___x_6194_);
if (v_isSharedCheck_6211_ == 0)
{
v___x_6206_ = v___x_6194_;
v_isShared_6207_ = v_isSharedCheck_6211_;
goto v_resetjp_6205_;
}
else
{
lean_inc(v_a_6204_);
lean_dec(v___x_6194_);
v___x_6206_ = lean_box(0);
v_isShared_6207_ = v_isSharedCheck_6211_;
goto v_resetjp_6205_;
}
v_resetjp_6205_:
{
lean_object* v___x_6209_; 
if (v_isShared_6207_ == 0)
{
v___x_6209_ = v___x_6206_;
goto v_reusejp_6208_;
}
else
{
lean_object* v_reuseFailAlloc_6210_; 
v_reuseFailAlloc_6210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6210_, 0, v_a_6204_);
v___x_6209_ = v_reuseFailAlloc_6210_;
goto v_reusejp_6208_;
}
v_reusejp_6208_:
{
return v___x_6209_;
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
lean_object* v_a_6239_; lean_object* v___x_6241_; uint8_t v_isShared_6242_; uint8_t v_isSharedCheck_6246_; 
lean_dec(v_a_6146_);
v_a_6239_ = lean_ctor_get(v___x_6147_, 0);
v_isSharedCheck_6246_ = !lean_is_exclusive(v___x_6147_);
if (v_isSharedCheck_6246_ == 0)
{
v___x_6241_ = v___x_6147_;
v_isShared_6242_ = v_isSharedCheck_6246_;
goto v_resetjp_6240_;
}
else
{
lean_inc(v_a_6239_);
lean_dec(v___x_6147_);
v___x_6241_ = lean_box(0);
v_isShared_6242_ = v_isSharedCheck_6246_;
goto v_resetjp_6240_;
}
v_resetjp_6240_:
{
lean_object* v___x_6244_; 
if (v_isShared_6242_ == 0)
{
v___x_6244_ = v___x_6241_;
goto v_reusejp_6243_;
}
else
{
lean_object* v_reuseFailAlloc_6245_; 
v_reuseFailAlloc_6245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6245_, 0, v_a_6239_);
v___x_6244_ = v_reuseFailAlloc_6245_;
goto v_reusejp_6243_;
}
v_reusejp_6243_:
{
return v___x_6244_;
}
}
}
}
}
}
else
{
lean_object* v_a_6248_; lean_object* v___x_6250_; uint8_t v_isShared_6251_; uint8_t v_isSharedCheck_6255_; 
lean_dec_ref(v_projectDir_6126_);
lean_dec_ref(v_lean_6124_);
v_a_6248_ = lean_ctor_get(v___x_6137_, 0);
v_isSharedCheck_6255_ = !lean_is_exclusive(v___x_6137_);
if (v_isSharedCheck_6255_ == 0)
{
v___x_6250_ = v___x_6137_;
v_isShared_6251_ = v_isSharedCheck_6255_;
goto v_resetjp_6249_;
}
else
{
lean_inc(v_a_6248_);
lean_dec(v___x_6137_);
v___x_6250_ = lean_box(0);
v_isShared_6251_ = v_isSharedCheck_6255_;
goto v_resetjp_6249_;
}
v_resetjp_6249_:
{
lean_object* v___x_6253_; 
if (v_isShared_6251_ == 0)
{
v___x_6253_ = v___x_6250_;
goto v_reusejp_6252_;
}
else
{
lean_object* v_reuseFailAlloc_6254_; 
v_reuseFailAlloc_6254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6254_, 0, v_a_6248_);
v___x_6253_ = v_reuseFailAlloc_6254_;
goto v_reusejp_6252_;
}
v_reusejp_6252_:
{
return v___x_6253_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Check_runCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_fromExport_x3f_6121_ = stack[0].m_obj;
uint8_t v_paranoid_6122_ = stack[1].m_num;
uint8_t v_inadvisablyNoSandbox_6123_ = stack[2].m_num;
lean_object* v_lean_6124_ = stack[3].m_obj;
lean_object* v_lake_6125_ = stack[4].m_obj;
lean_object* v_projectDir_6126_ = stack[5].m_obj;
lean_object* v_res_6256_;
v_res_6256_ = l_Lake_Check_runCheck(v_fromExport_x3f_6121_, v_paranoid_6122_, v_inadvisablyNoSandbox_6123_, v_lean_6124_, v_lake_6125_, v_projectDir_6126_);
stack->m_obj
 = v_res_6256_;
}
LEAN_EXPORT lean_object* l_Lake_Check_runCheck___boxed(lean_object* v_fromExport_x3f_6257_, lean_object* v_paranoid_6258_, lean_object* v_inadvisablyNoSandbox_6259_, lean_object* v_lean_6260_, lean_object* v_lake_6261_, lean_object* v_projectDir_6262_, lean_object* v_a_6263_){
_start:
{
uint8_t v_paranoid_boxed_6264_; uint8_t v_inadvisablyNoSandbox_boxed_6265_; lean_object* v_res_6266_; 
v_paranoid_boxed_6264_ = lean_unbox(v_paranoid_6258_);
v_inadvisablyNoSandbox_boxed_6265_ = lean_unbox(v_inadvisablyNoSandbox_6259_);
v_res_6266_ = l_Lake_Check_runCheck(v_fromExport_x3f_6257_, v_paranoid_boxed_6264_, v_inadvisablyNoSandbox_boxed_6265_, v_lean_6260_, v_lake_6261_, v_projectDir_6262_);
lean_dec_ref(v_lake_6261_);
return v_res_6266_;
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
