// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: public import Lake.Config.Workspace import Lake.Build.Run import Lake.Build.Actions import Lake.Build.Targets import Lake.Build.Module import Lake.Util.Proc
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
extern lean_object* l_Lake_LeanExe_exeFacet;
extern lean_object* l_Lake_LeanExe_keyword;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_toName(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_prepareLeanCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
static const lean_ctor_object l_Lake_env___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_env___closed__0 = (const lean_object*)&l_Lake_env___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_env___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_exe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown executable `"};
static const lean_object* l_Lake_exe___closed__0 = (const lean_object*)&l_Lake_exe___closed__0_value;
static const lean_string_object l_Lake_exe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lake_exe___closed__1 = (const lean_object*)&l_Lake_exe___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_pack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "packing "};
static const lean_object* l_Lake_Package_pack___closed__0 = (const lean_object*)&l_Lake_Package_pack___closed__0_value;
static const lean_array_object l_Lake_Package_pack___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_pack___closed__1 = (const lean_object*)&l_Lake_Package_pack___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_unpack___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "unpacking "};
static const lean_object* l_Lake_Package_unpack___closed__0 = (const lean_object*)&l_Lake_Package_unpack___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_unpack___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_uploadRelease___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gh"};
static const lean_object* l_Lake_Package_uploadRelease___closed__0 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__0_value;
static const lean_array_object l_Lake_Package_uploadRelease___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_uploadRelease___closed__1 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__1_value;
static const lean_string_object l_Lake_Package_uploadRelease___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "uploading "};
static const lean_object* l_Lake_Package_uploadRelease___closed__2 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__2_value;
static const lean_string_object l_Lake_Package_uploadRelease___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_Package_uploadRelease___closed__3 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__3_value;
static const lean_string_object l_Lake_Package_uploadRelease___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "release"};
static const lean_object* l_Lake_Package_uploadRelease___closed__4 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__4_value;
static const lean_string_object l_Lake_Package_uploadRelease___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "upload"};
static const lean_object* l_Lake_Package_uploadRelease___closed__5 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__5_value;
static const lean_string_object l_Lake_Package_uploadRelease___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--clobber"};
static const lean_object* l_Lake_Package_uploadRelease___closed__6 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__6_value;
static lean_once_cell_t l_Lake_Package_uploadRelease___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_uploadRelease___closed__7;
static lean_once_cell_t l_Lake_Package_uploadRelease___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_uploadRelease___closed__8;
static const lean_string_object l_Lake_Package_uploadRelease___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-R"};
static const lean_object* l_Lake_Package_uploadRelease___closed__9 = (const lean_object*)&l_Lake_Package_uploadRelease___closed__9_value;
static lean_once_cell_t l_Lake_Package_uploadRelease___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_uploadRelease___closed__10;
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___boxed(lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_resolveDriver___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": invalid "};
static const lean_object* l_Lake_Package_resolveDriver___closed__0 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__0_value;
static const lean_string_object l_Lake_Package_resolveDriver___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " driver '"};
static const lean_object* l_Lake_Package_resolveDriver___closed__1 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__1_value;
static const lean_string_object l_Lake_Package_resolveDriver___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "' (too many '/')"};
static const lean_object* l_Lake_Package_resolveDriver___closed__2 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__2_value;
static const lean_string_object l_Lake_Package_resolveDriver___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ": unknown "};
static const lean_object* l_Lake_Package_resolveDriver___closed__3 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__3_value;
static const lean_string_object l_Lake_Package_resolveDriver___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " driver package '"};
static const lean_object* l_Lake_Package_resolveDriver___closed__4 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__4_value;
static const lean_string_object l_Lake_Package_resolveDriver___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_Package_resolveDriver___closed__5 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__5_value;
static const lean_string_object l_Lake_Package_resolveDriver___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ": no "};
static const lean_object* l_Lake_Package_resolveDriver___closed__6 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__6_value;
static const lean_string_object l_Lake_Package_resolveDriver___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " driver configured"};
static const lean_object* l_Lake_Package_resolveDriver___closed__7 = (const lean_object*)&l_Lake_Package_resolveDriver___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_test___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "test"};
static const lean_object* l_Lake_Package_test___closed__0 = (const lean_object*)&l_Lake_Package_test___closed__0_value;
static const lean_string_object l_Lake_Package_test___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = ": arguments cannot be passed to a library test driver"};
static const lean_object* l_Lake_Package_test___closed__1 = (const lean_object*)&l_Lake_Package_test___closed__1_value;
static const lean_string_object l_Lake_Package_test___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = ": invalid test driver: unknown script, executable, or library '"};
static const lean_object* l_Lake_Package_test___closed__2 = (const lean_object*)&l_Lake_Package_test___closed__2_value;
static const lean_string_object l_Lake_Package_test___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_Package_test___closed__3 = (const lean_object*)&l_Lake_Package_test___closed__3_value;
static const lean_ctor_object l_Lake_Package_test___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_test___closed__3_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake_Package_test___closed__4 = (const lean_object*)&l_Lake_Package_test___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_lint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lint"};
static const lean_object* l_Lake_Package_lint___closed__0 = (const lean_object*)&l_Lake_Package_lint___closed__0_value;
static const lean_string_object l_Lake_Package_lint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = ": invalid lint driver: unknown script or executable '"};
static const lean_object* l_Lake_Package_lint___closed__1 = (const lean_object*)&l_Lake_Package_lint___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_env(lean_object* v_cmd_3_, lean_object* v_args_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc(v_a_5_);
v___x_7_ = l_Lake_Workspace_augmentedEnvVars(v_a_5_);
v___x_8_ = ((lean_object*)(l_Lake_env___closed__0));
v___x_9_ = lean_box(0);
v___x_10_ = 1;
v___x_11_ = 0;
v___x_12_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_12_, 0, v___x_8_);
lean_ctor_set(v___x_12_, 1, v_cmd_3_);
lean_ctor_set(v___x_12_, 2, v_args_4_);
lean_ctor_set(v___x_12_, 3, v___x_9_);
lean_ctor_set(v___x_12_, 4, v___x_7_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*5, v___x_10_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*5 + 1, v___x_11_);
v___x_13_ = lean_io_process_spawn(v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
v___x_15_ = lean_io_process_child_wait(v___x_8_, v_a_14_);
lean_dec(v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_23_; 
v_a_16_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
v___x_18_ = v___x_13_;
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_13_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_21_; 
if (v_isShared_19_ == 0)
{
v___x_21_ = v___x_18_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_a_16_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_env___boxed(lean_object* v_cmd_24_, lean_object* v_args_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_env(v_cmd_24_, v_args_25_, v_a_26_);
lean_dec(v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__0(lean_object* v_val_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_pkg_37_; lean_object* v_name_38_; lean_object* v_keyName_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_pkg_37_ = lean_ctor_get(v_val_29_, 0);
v_name_38_ = lean_ctor_get(v_val_29_, 1);
v_keyName_39_ = lean_ctor_get(v_pkg_37_, 2);
v___x_40_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_38_);
lean_inc(v_keyName_39_);
v___x_41_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_41_, 0, v_keyName_39_);
lean_ctor_set(v___x_41_, 1, v_name_38_);
v___x_42_ = l_Lake_LeanExe_keyword;
v___x_43_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
lean_ctor_set(v___x_43_, 2, v_val_29_);
lean_ctor_set(v___x_43_, 3, v___x_40_);
v___x_44_ = lean_apply_7(v___y_30_, v___x_43_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, lean_box(0));
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object* v_val_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lake_exe___lam__0(v_val_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_exe(lean_object* v_name_56_, lean_object* v_args_57_, lean_object* v_buildConfig_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lake_Workspace_findLeanExe_x3f(v_name_56_, v_a_59_);
if (lean_obj_tag(v___x_61_) == 1)
{
lean_object* v_val_62_; lean_object* v___f_63_; lean_object* v___x_64_; 
lean_dec(v_name_56_);
v_val_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_val_62_);
lean_dec_ref_known(v___x_61_, 1);
v___f_63_ = lean_alloc_closure((void*)(l_Lake_exe___lam__0___boxed), 8, 1);
lean_closure_set(v___f_63_, 0, v_val_62_);
lean_inc(v_a_59_);
v___x_64_ = l_Lake_Workspace_runBuild___redArg(v_a_59_, v___f_63_, v_buildConfig_58_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_66_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v___x_64_, 1);
v___x_66_ = l_Lake_env(v_a_65_, v_args_57_, v_a_59_);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec_ref(v_args_57_);
v_a_67_ = lean_ctor_get(v___x_64_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_64_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_64_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v___x_61_);
lean_dec_ref(v_buildConfig_58_);
lean_dec_ref(v_args_57_);
v___x_75_ = ((lean_object*)(l_Lake_exe___closed__0));
v___x_76_ = 1;
v___x_77_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_56_, v___x_76_);
v___x_78_ = lean_string_append(v___x_75_, v___x_77_);
lean_dec_ref(v___x_77_);
v___x_79_ = ((lean_object*)(l_Lake_exe___closed__1));
v___x_80_ = lean_string_append(v___x_78_, v___x_79_);
v___x_81_ = lean_mk_io_user_error(v___x_80_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_exe___boxed(lean_object* v_name_83_, lean_object* v_args_84_, lean_object* v_buildConfig_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lake_exe(v_name_83_, v_args_84_, v_buildConfig_85_, v_a_86_);
lean_dec(v_a_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object* v_pkg_92_, lean_object* v_file_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_config_96_; lean_object* v_dir_97_; lean_object* v_buildDir_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_config_96_ = lean_ctor_get(v_pkg_92_, 6);
lean_inc_ref(v_config_96_);
v_dir_97_ = lean_ctor_get(v_pkg_92_, 4);
lean_inc_ref(v_dir_97_);
lean_dec_ref(v_pkg_92_);
v_buildDir_98_ = lean_ctor_get(v_config_96_, 5);
lean_inc_ref(v_buildDir_98_);
lean_dec_ref(v_config_96_);
v___x_99_ = ((lean_object*)(l_Lake_Package_pack___closed__0));
v___x_100_ = lean_string_append(v___x_99_, v_file_93_);
v___x_101_ = 1;
v___x_102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = lean_array_push(v_a_94_, v___x_102_);
v___x_104_ = l_System_FilePath_normalize(v_buildDir_98_);
v___x_105_ = l_Lake_joinRelative(v_dir_97_, v___x_104_);
v___x_106_ = 1;
v___x_107_ = ((lean_object*)(l_Lake_Package_pack___closed__1));
v___x_108_ = l_Lake_tar(v___x_105_, v_file_93_, v___x_106_, v___x_107_, v___x_103_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pack___boxed(lean_object* v_pkg_109_, lean_object* v_file_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lake_Package_pack(v_pkg_109_, v_file_110_, v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object* v_pkg_115_, lean_object* v_file_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_config_119_; lean_object* v_dir_120_; lean_object* v_buildDir_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; lean_object* v___x_130_; 
v_config_119_ = lean_ctor_get(v_pkg_115_, 6);
lean_inc_ref(v_config_119_);
v_dir_120_ = lean_ctor_get(v_pkg_115_, 4);
lean_inc_ref(v_dir_120_);
lean_dec_ref(v_pkg_115_);
v_buildDir_121_ = lean_ctor_get(v_config_119_, 5);
lean_inc_ref(v_buildDir_121_);
lean_dec_ref(v_config_119_);
v___x_122_ = ((lean_object*)(l_Lake_Package_unpack___closed__0));
v___x_123_ = lean_string_append(v___x_122_, v_file_116_);
v___x_124_ = 1;
v___x_125_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = lean_array_push(v_a_117_, v___x_125_);
v___x_127_ = l_System_FilePath_normalize(v_buildDir_121_);
v___x_128_ = l_Lake_joinRelative(v_dir_120_, v___x_127_);
v___x_129_ = 1;
v___x_130_ = l_Lake_untar(v_file_116_, v___x_128_, v___x_129_, v___x_126_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_unpack___boxed(lean_object* v_pkg_131_, lean_object* v_file_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lake_Package_unpack(v_pkg_131_, v_file_132_, v_a_133_);
return v_res_135_;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__7(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__4));
v___x_145_ = lean_unsigned_to_nat(5u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_array_push(v___x_146_, v___x_144_);
return v___x_147_;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__8(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__5));
v___x_149_ = lean_obj_once(&l_Lake_Package_uploadRelease___closed__7, &l_Lake_Package_uploadRelease___closed__7_once, _init_l_Lake_Package_uploadRelease___closed__7);
v___x_150_ = lean_array_push(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__10(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__9));
v___x_153_ = lean_unsigned_to_nat(2u);
v___x_154_ = lean_mk_empty_array_with_capacity(v___x_153_);
v___x_155_ = lean_array_push(v___x_154_, v___x_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object* v_pkg_156_, lean_object* v_tag_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_args_161_; lean_object* v___y_162_; lean_object* v_dir_171_; lean_object* v_config_172_; lean_object* v_buildArchive_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_dir_171_ = lean_ctor_get(v_pkg_156_, 4);
v_config_172_ = lean_ctor_get(v_pkg_156_, 6);
lean_inc_ref(v_config_172_);
v_buildArchive_173_ = lean_ctor_get(v_pkg_156_, 21);
lean_inc_ref_n(v_buildArchive_173_, 2);
v___x_174_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_171_);
v___x_175_ = l_Lake_joinRelative(v_dir_171_, v___x_174_);
v___x_176_ = l_Lake_joinRelative(v___x_175_, v_buildArchive_173_);
lean_inc_ref(v___x_176_);
v___x_177_ = l_Lake_Package_pack(v_pkg_156_, v___x_176_, v_a_158_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v_releaseRepo_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_a_178_ = lean_ctor_get(v___x_177_, 1);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 2);
v_releaseRepo_179_ = lean_ctor_get(v_config_172_, 10);
lean_inc(v_releaseRepo_179_);
lean_dec_ref(v_config_172_);
v___x_180_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__2));
v___x_181_ = lean_string_append(v___x_180_, v_tag_157_);
v___x_182_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__3));
v___x_183_ = lean_string_append(v___x_181_, v___x_182_);
v___x_184_ = lean_string_append(v___x_183_, v_buildArchive_173_);
lean_dec_ref(v_buildArchive_173_);
v___x_185_ = 1;
v___x_186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_185_);
v___x_187_ = lean_array_push(v_a_178_, v___x_186_);
v___x_188_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__6));
v___x_189_ = lean_obj_once(&l_Lake_Package_uploadRelease___closed__8, &l_Lake_Package_uploadRelease___closed__8_once, _init_l_Lake_Package_uploadRelease___closed__8);
v___x_190_ = lean_array_push(v___x_189_, v_tag_157_);
v___x_191_ = lean_array_push(v___x_190_, v___x_176_);
v___x_192_ = lean_array_push(v___x_191_, v___x_188_);
if (lean_obj_tag(v_releaseRepo_179_) == 1)
{
lean_object* v_val_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_val_193_ = lean_ctor_get(v_releaseRepo_179_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v_releaseRepo_179_, 1);
v___x_194_ = lean_obj_once(&l_Lake_Package_uploadRelease___closed__10, &l_Lake_Package_uploadRelease___closed__10_once, _init_l_Lake_Package_uploadRelease___closed__10);
v___x_195_ = lean_array_push(v___x_194_, v_val_193_);
v___x_196_ = l_Array_append___redArg(v___x_192_, v___x_195_);
lean_dec_ref(v___x_195_);
v_args_161_ = v___x_196_;
v___y_162_ = v___x_187_;
goto v___jp_160_;
}
else
{
lean_dec(v_releaseRepo_179_);
v_args_161_ = v___x_192_;
v___y_162_ = v___x_187_;
goto v___jp_160_;
}
}
else
{
lean_dec_ref(v___x_176_);
lean_dec_ref(v_buildArchive_173_);
lean_dec_ref(v_config_172_);
lean_dec_ref(v_tag_157_);
return v___x_177_;
}
v___jp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_163_ = ((lean_object*)(l_Lake_env___closed__0));
v___x_164_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__0));
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__1));
v___x_167_ = 1;
v___x_168_ = 0;
v___x_169_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_169_, 0, v___x_163_);
lean_ctor_set(v___x_169_, 1, v___x_164_);
lean_ctor_set(v___x_169_, 2, v_args_161_);
lean_ctor_set(v___x_169_, 3, v___x_165_);
lean_ctor_set(v___x_169_, 4, v___x_166_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5, v___x_167_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5 + 1, v___x_168_);
v___x_170_ = l_Lake_proc(v___x_169_, v___x_168_, v___x_165_, v___y_162_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___boxed(lean_object* v_pkg_197_, lean_object* v_tag_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_Package_uploadRelease(v_pkg_197_, v_tag_198_, v_a_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg(){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___closed__0));
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___boxed(lean_object* v___dummy_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg();
return v_res_207_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0(void){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg();
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(lean_object* v_s_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___boxed(lean_object* v_s_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(v_s_211_);
lean_dec_ref(v_s_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(lean_object* v___x_216_, lean_object* v_as_217_, size_t v_sz_218_, size_t v_i_219_, lean_object* v_b_220_){
_start:
{
uint8_t v___x_221_; 
v___x_221_ = lean_usize_dec_lt(v_i_219_, v_sz_218_);
if (v___x_221_ == 0)
{
lean_inc_ref(v_b_220_);
return v_b_220_;
}
else
{
lean_object* v_a_222_; lean_object* v_baseName_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_a_222_ = lean_array_uget_borrowed(v_as_217_, v_i_219_);
v_baseName_223_ = lean_ctor_get(v_a_222_, 1);
v___x_224_ = lean_box(0);
v___x_225_ = lean_name_eq(v_baseName_223_, v___x_216_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; size_t v___x_227_; size_t v___x_228_; 
v___x_226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0));
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_add(v_i_219_, v___x_227_);
v_i_219_ = v___x_228_;
v_b_220_ = v___x_226_;
goto _start;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
lean_inc(v_a_222_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v_a_222_);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_224_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___boxed(lean_object* v___x_233_, lean_object* v_as_234_, lean_object* v_sz_235_, lean_object* v_i_236_, lean_object* v_b_237_){
_start:
{
size_t v_sz_boxed_238_; size_t v_i_boxed_239_; lean_object* v_res_240_; 
v_sz_boxed_238_ = lean_unbox_usize(v_sz_235_);
lean_dec(v_sz_235_);
v_i_boxed_239_ = lean_unbox_usize(v_i_236_);
lean_dec(v_i_236_);
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_233_, v_as_234_, v_sz_boxed_238_, v_i_boxed_239_, v_b_237_);
lean_dec_ref(v_b_237_);
lean_dec_ref(v_as_234_);
lean_dec(v___x_233_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(lean_object* v_driver_241_, lean_object* v___x_242_, lean_object* v___x_243_, lean_object* v_a_244_, lean_object* v_b_245_){
_start:
{
lean_object* v_it_247_; lean_object* v_startInclusive_248_; lean_object* v_endExclusive_249_; 
if (lean_obj_tag(v_a_244_) == 0)
{
lean_object* v_currPos_254_; lean_object* v_searcher_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_278_; 
v_currPos_254_ = lean_ctor_get(v_a_244_, 0);
v_searcher_255_ = lean_ctor_get(v_a_244_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_a_244_);
if (v_isSharedCheck_278_ == 0)
{
v___x_257_ = v_a_244_;
v_isShared_258_ = v_isSharedCheck_278_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_searcher_255_);
lean_inc(v_currPos_254_);
lean_dec(v_a_244_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_278_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
uint8_t v_decide_259_; 
v_decide_259_ = lean_nat_dec_eq(v_searcher_255_, v___x_243_);
if (v_decide_259_ == 0)
{
uint32_t v___x_260_; uint32_t v___x_261_; uint8_t v___x_262_; 
v___x_260_ = 47;
v___x_261_ = lean_string_utf8_get_fast(v_driver_241_, v_searcher_255_);
v___x_262_ = lean_uint32_dec_eq(v___x_261_, v___x_260_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_string_utf8_next_fast(v_driver_241_, v_searcher_255_);
lean_dec(v_searcher_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_263_);
v___x_265_ = v___x_257_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_currPos_254_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_267_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
v_a_244_ = v___x_265_;
goto _start;
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_slice_271_; lean_object* v_nextIt_273_; 
v___x_268_ = lean_string_utf8_next_fast(v_driver_241_, v_searcher_255_);
v___x_269_ = lean_nat_sub(v___x_268_, v_searcher_255_);
v___x_270_ = lean_nat_add(v_searcher_255_, v___x_269_);
lean_dec(v___x_269_);
v_slice_271_ = l_String_Slice_subslice_x21(v___x_242_, v_currPos_254_, v_searcher_255_);
lean_inc(v___x_270_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v___x_270_);
lean_ctor_set(v___x_257_, 0, v___x_270_);
v_nextIt_273_ = v___x_257_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_270_);
v_nextIt_273_ = v_reuseFailAlloc_276_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v_startInclusive_274_; lean_object* v_endExclusive_275_; 
v_startInclusive_274_ = lean_ctor_get(v_slice_271_, 0);
lean_inc(v_startInclusive_274_);
v_endExclusive_275_ = lean_ctor_get(v_slice_271_, 1);
lean_inc(v_endExclusive_275_);
lean_dec_ref(v_slice_271_);
v_it_247_ = v_nextIt_273_;
v_startInclusive_248_ = v_startInclusive_274_;
v_endExclusive_249_ = v_endExclusive_275_;
goto v___jp_246_;
}
}
}
else
{
lean_object* v___x_277_; 
lean_del_object(v___x_257_);
lean_dec(v_searcher_255_);
v___x_277_ = lean_box(1);
lean_inc(v___x_243_);
v_it_247_ = v___x_277_;
v_startInclusive_248_ = v_currPos_254_;
v_endExclusive_249_ = v___x_243_;
goto v___jp_246_;
}
}
}
else
{
lean_dec(v___x_243_);
lean_dec_ref(v_driver_241_);
return v_b_245_;
}
v___jp_246_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_inc_ref(v_driver_241_);
v___x_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_250_, 0, v_driver_241_);
lean_ctor_set(v___x_250_, 1, v_startInclusive_248_);
lean_ctor_set(v___x_250_, 2, v_endExclusive_249_);
v___x_251_ = l_String_Slice_toString(v___x_250_);
lean_dec_ref_known(v___x_250_, 3);
v___x_252_ = lean_array_push(v_b_245_, v___x_251_);
v_a_244_ = v_it_247_;
v_b_245_ = v___x_252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object* v_driver_279_, lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_279_, v___x_280_, v___x_281_, v_a_282_, v_b_283_);
lean_dec_ref(v___x_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object* v_pkg_293_, lean_object* v_kind_294_, lean_object* v_driver_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = lean_string_utf8_byte_size(v_driver_295_);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_nat_dec_eq(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_inc_ref_n(v_driver_295_, 2);
v___x_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_314_, 0, v_driver_295_);
lean_ctor_set(v___x_314_, 1, v___x_299_);
lean_ctor_set(v___x_314_, 2, v___x_298_);
v___x_315_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0);
v___x_316_ = ((lean_object*)(l_Lake_Package_pack___closed__1));
v___x_317_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_295_, v___x_314_, v___x_298_, v___x_315_, v___x_316_);
lean_dec_ref_known(v___x_314_, 3);
v___x_318_ = lean_array_to_list(v___x_317_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_head_319_; lean_object* v_tail_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_367_; 
v_head_319_ = lean_ctor_get(v___x_318_, 0);
v_tail_320_ = lean_ctor_get(v___x_318_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_367_ == 0)
{
v___x_322_ = v___x_318_;
v_isShared_323_ = v_isSharedCheck_367_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_tail_320_);
lean_inc(v_head_319_);
lean_dec(v___x_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_367_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
if (lean_obj_tag(v_tail_320_) == 0)
{
lean_object* v___x_338_; 
lean_dec_ref(v_driver_295_);
if (v_isShared_323_ == 0)
{
lean_ctor_set_tag(v___x_322_, 0);
lean_ctor_set(v___x_322_, 1, v_head_319_);
lean_ctor_set(v___x_322_, 0, v_pkg_293_);
v___x_338_ = v___x_322_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_pkg_293_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_head_319_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
else
{
lean_object* v_tail_341_; 
lean_del_object(v___x_322_);
v_tail_341_ = lean_ctor_get(v_tail_320_, 1);
if (lean_obj_tag(v_tail_341_) == 0)
{
lean_object* v_head_342_; lean_object* v_packages_343_; lean_object* v___x_344_; lean_object* v___x_345_; size_t v_sz_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v_fst_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_driver_295_);
v_head_342_ = lean_ctor_get(v_tail_320_, 0);
lean_inc(v_head_342_);
lean_dec_ref_known(v_tail_320_, 2);
v_packages_343_ = lean_ctor_get(v_a_296_, 4);
lean_inc(v_head_319_);
v___x_344_ = l_String_toName(v_head_319_);
v___x_345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0));
v_sz_346_ = lean_array_size(v_packages_343_);
v___x_347_ = ((size_t)0ULL);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_344_, v_packages_343_, v_sz_346_, v___x_347_, v___x_345_);
lean_dec(v___x_344_);
v_fst_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v___x_348_, 1);
lean_dec(v_unused_366_);
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_365_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_fst_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_365_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
if (lean_obj_tag(v_fst_349_) == 0)
{
lean_del_object(v___x_351_);
lean_dec(v_head_342_);
goto v___jp_324_;
}
else
{
lean_object* v_val_353_; 
v_val_353_ = lean_ctor_get(v_fst_349_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v_fst_349_, 1);
if (lean_obj_tag(v_val_353_) == 1)
{
lean_object* v_val_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_head_319_);
lean_dec_ref(v_pkg_293_);
v_val_354_ = lean_ctor_get(v_val_353_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v_val_353_);
if (v_isSharedCheck_364_ == 0)
{
v___x_356_ = v_val_353_;
v_isShared_357_ = v_isSharedCheck_364_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_val_354_);
lean_dec(v_val_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_364_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v_head_342_);
lean_ctor_set(v___x_351_, 0, v_val_354_);
v___x_359_ = v___x_351_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_val_354_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_head_342_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 0);
lean_ctor_set(v___x_356_, 0, v___x_359_);
v___x_361_ = v___x_356_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
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
lean_dec(v_val_353_);
lean_del_object(v___x_351_);
lean_dec(v_head_342_);
goto v___jp_324_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_320_, 2);
lean_dec(v_head_319_);
goto v___jp_301_;
}
}
v___jp_324_:
{
lean_object* v_baseName_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_baseName_325_ = lean_ctor_get(v_pkg_293_, 1);
lean_inc(v_baseName_325_);
lean_dec_ref(v_pkg_293_);
v___x_326_ = l_Lean_Name_toString(v_baseName_325_, v___x_300_);
v___x_327_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__3));
v___x_328_ = lean_string_append(v___x_326_, v___x_327_);
v___x_329_ = lean_string_append(v___x_328_, v_kind_294_);
v___x_330_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__4));
v___x_331_ = lean_string_append(v___x_329_, v___x_330_);
v___x_332_ = lean_string_append(v___x_331_, v_head_319_);
lean_dec(v_head_319_);
v___x_333_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_334_ = lean_string_append(v___x_332_, v___x_333_);
v___x_335_ = lean_mk_io_user_error(v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
}
else
{
lean_dec(v___x_318_);
goto v___jp_301_;
}
}
else
{
lean_object* v_baseName_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec_ref(v_driver_295_);
v_baseName_368_ = lean_ctor_get(v_pkg_293_, 1);
lean_inc(v_baseName_368_);
lean_dec_ref(v_pkg_293_);
v___x_369_ = 0;
v___x_370_ = l_Lean_Name_toString(v_baseName_368_, v___x_369_);
v___x_371_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__6));
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
v___x_373_ = lean_string_append(v___x_372_, v_kind_294_);
v___x_374_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__7));
v___x_375_ = lean_string_append(v___x_373_, v___x_374_);
v___x_376_ = lean_mk_io_user_error(v___x_375_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
v___jp_301_:
{
lean_object* v_baseName_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_baseName_302_ = lean_ctor_get(v_pkg_293_, 1);
lean_inc(v_baseName_302_);
lean_dec_ref(v_pkg_293_);
v___x_303_ = l_Lean_Name_toString(v_baseName_302_, v___x_300_);
v___x_304_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__0));
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
v___x_306_ = lean_string_append(v___x_305_, v_kind_294_);
v___x_307_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__1));
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
v___x_309_ = lean_string_append(v___x_308_, v_driver_295_);
lean_dec_ref(v_driver_295_);
v___x_310_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__2));
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
v___x_312_ = lean_mk_io_user_error(v___x_311_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object* v_pkg_378_, lean_object* v_kind_379_, lean_object* v_driver_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lake_Package_resolveDriver(v_pkg_378_, v_kind_379_, v_driver_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_kind_379_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(lean_object* v_driver_384_, lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v_inst_387_, lean_object* v_R_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_384_, v___x_385_, v___x_386_, v_a_389_, v_b_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___boxed(lean_object* v_driver_392_, lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v_inst_395_, lean_object* v_R_396_, lean_object* v_a_397_, lean_object* v_b_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(v_driver_392_, v___x_393_, v___x_394_, v_inst_395_, v_R_396_, v_a_397_, v_b_398_);
lean_dec_ref(v___x_393_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object* v_keyName_400_, lean_object* v_name_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = l_Lake_LeanLib_defaultFacet;
v___x_412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_412_, 0, v_keyName_400_);
lean_ctor_set(v___x_412_, 1, v_name_401_);
v___x_413_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_402_);
lean_ctor_set(v___x_413_, 2, v___x_403_);
lean_ctor_set(v___x_413_, 3, v___x_411_);
v___x_414_ = lean_apply_7(v___y_404_, v___x_413_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, lean_box(0));
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0___boxed(lean_object* v_keyName_415_, lean_object* v_name_416_, lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lake_Package_test___lam__0(v_keyName_415_, v_name_416_, v___x_417_, v___x_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object* v_keyName_427_, lean_object* v_name_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_438_ = l_Lake_LeanExe_exeFacet;
v___x_439_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_439_, 0, v_keyName_427_);
lean_ctor_set(v___x_439_, 1, v_name_428_);
v___x_440_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_429_);
lean_ctor_set(v___x_440_, 2, v___x_430_);
lean_ctor_set(v___x_440_, 3, v___x_438_);
v___x_441_ = lean_apply_7(v___y_431_, v___x_440_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, lean_box(0));
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1___boxed(lean_object* v_keyName_442_, lean_object* v_name_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lake_Package_test___lam__1(v_keyName_442_, v_name_443_, v___x_444_, v___x_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v_res_453_;
}
}
static lean_object* _init_l_Lake_Package_test___boxed__const__1(void){
_start:
{
uint32_t v___x_460_; lean_object* v___x_461_; 
v___x_460_ = 0;
v___x_461_ = lean_box_uint32(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* v_pkg_462_, lean_object* v_args_463_, lean_object* v_buildConfig_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_config_467_; lean_object* v_testDriver_468_; lean_object* v_testDriverArgs_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_config_467_ = lean_ctor_get(v_pkg_462_, 6);
v_testDriver_468_ = lean_ctor_get(v_pkg_462_, 22);
lean_inc_ref(v_testDriver_468_);
v_testDriverArgs_469_ = lean_ctor_get(v_config_467_, 13);
lean_inc_ref(v_testDriverArgs_469_);
v___x_470_ = ((lean_object*)(l_Lake_Package_test___closed__0));
v___x_471_ = l_Lake_Package_resolveDriver(v_pkg_462_, v___x_470_, v_testDriver_468_, v_a_465_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_594_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_594_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_594_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_594_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v_baseName_478_; lean_object* v_keyName_479_; lean_object* v_scripts_480_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_fst_476_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_fst_476_);
v_snd_477_ = lean_ctor_get(v_a_472_, 1);
lean_inc_n(v_snd_477_, 2);
lean_dec(v_a_472_);
v_baseName_478_ = lean_ctor_get(v_fst_476_, 1);
v_keyName_479_ = lean_ctor_get(v_fst_476_, 2);
lean_inc(v_keyName_479_);
v_scripts_480_ = lean_ctor_get(v_fst_476_, 18);
v___x_566_ = l_String_toName(v_snd_477_);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_480_, v___x_566_);
if (lean_obj_tag(v___x_567_) == 1)
{
lean_object* v_val_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_566_);
lean_dec(v_keyName_479_);
lean_dec(v_snd_477_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec_ref(v_buildConfig_464_);
v_val_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = lean_array_to_list(v_testDriverArgs_469_);
v___x_570_ = l_List_appendTR___redArg(v___x_569_, v_args_463_);
v___x_571_ = l_Lake_Script_run(v___x_570_, v_val_568_, v_a_465_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; 
lean_dec(v___x_567_);
v___x_572_ = l_Lake_Package_findTargetDecl_x3f(v___x_566_, v_fst_476_);
lean_dec(v___x_566_);
if (lean_obj_tag(v___x_572_) == 0)
{
goto v___jp_553_;
}
else
{
lean_object* v_val_573_; lean_object* v_name_574_; lean_object* v_kind_575_; lean_object* v_config_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_val_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v___x_572_, 1);
v_name_574_ = lean_ctor_get(v_val_573_, 1);
lean_inc(v_name_574_);
v_kind_575_ = lean_ctor_get(v_val_573_, 2);
lean_inc(v_kind_575_);
v_config_576_ = lean_ctor_get(v_val_573_, 3);
lean_inc(v_config_576_);
lean_dec(v_val_573_);
v___x_577_ = l_Lake_LeanExe_keyword;
v___x_578_ = lean_name_eq(v_kind_575_, v___x_577_);
lean_dec(v_kind_575_);
if (v___x_578_ == 0)
{
lean_dec(v_config_576_);
lean_dec(v_name_574_);
goto v___jp_553_;
}
else
{
lean_object* v___x_579_; lean_object* v___f_580_; lean_object* v___x_581_; 
lean_dec(v_snd_477_);
lean_del_object(v___x_474_);
lean_inc(v_name_574_);
v___x_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_579_, 0, v_fst_476_);
lean_ctor_set(v___x_579_, 1, v_name_574_);
lean_ctor_set(v___x_579_, 2, v_config_576_);
v___f_580_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_580_, 0, v_keyName_479_);
lean_closure_set(v___f_580_, 1, v_name_574_);
lean_closure_set(v___f_580_, 2, v___x_577_);
lean_closure_set(v___f_580_, 3, v___x_579_);
lean_inc(v_a_465_);
v___x_581_ = l_Lake_Workspace_runBuild___redArg(v_a_465_, v___f_580_, v_buildConfig_464_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = lean_array_mk(v_args_463_);
v___x_584_ = l_Array_append___redArg(v_testDriverArgs_469_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = l_Lake_env(v_a_582_, v___x_584_, v_a_465_);
return v___x_585_;
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_testDriverArgs_469_);
lean_dec(v_args_463_);
v_a_586_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_581_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_581_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
}
v___jp_481_:
{
if (v___y_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
lean_inc(v_baseName_478_);
lean_dec(v___y_485_);
lean_dec(v___y_484_);
lean_dec(v___y_482_);
lean_dec(v_keyName_479_);
lean_dec(v_fst_476_);
lean_dec_ref(v_buildConfig_464_);
v___x_487_ = l_Lean_Name_toString(v_baseName_478_, v___y_486_);
v___x_488_ = ((lean_object*)(l_Lake_Package_test___closed__1));
v___x_489_ = lean_string_append(v___x_487_, v___x_488_);
v___x_490_ = lean_mk_io_user_error(v___x_489_);
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 1);
lean_ctor_set(v___x_474_, 0, v___x_490_);
v___x_492_ = v___x_474_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v_toLogConfig_494_; uint8_t v_oldMode_495_; uint8_t v_trustHash_496_; uint8_t v_noBuild_497_; uint8_t v_failFast_498_; uint8_t v_verbosity_499_; uint8_t v_showSuccess_500_; lean_object* v_outputsFile_x3f_501_; lean_object* v_leanOptOverrides_502_; lean_object* v_macosxDeploymentTarget_x3f_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_542_; 
lean_del_object(v___x_474_);
v_toLogConfig_494_ = lean_ctor_get(v_buildConfig_464_, 0);
v_oldMode_495_ = lean_ctor_get_uint8(v_buildConfig_464_, sizeof(void*)*4);
v_trustHash_496_ = lean_ctor_get_uint8(v_buildConfig_464_, sizeof(void*)*4 + 1);
v_noBuild_497_ = lean_ctor_get_uint8(v_buildConfig_464_, sizeof(void*)*4 + 2);
v_failFast_498_ = lean_ctor_get_uint8(v_buildConfig_464_, sizeof(void*)*4 + 3);
v_verbosity_499_ = lean_ctor_get_uint8(v_buildConfig_464_, sizeof(void*)*4 + 4);
v_showSuccess_500_ = lean_ctor_get_uint8(v_buildConfig_464_, sizeof(void*)*4 + 5);
v_outputsFile_x3f_501_ = lean_ctor_get(v_buildConfig_464_, 1);
v_leanOptOverrides_502_ = lean_ctor_get(v_buildConfig_464_, 2);
v_macosxDeploymentTarget_x3f_503_ = lean_ctor_get(v_buildConfig_464_, 3);
v_isSharedCheck_542_ = !lean_is_exclusive(v_buildConfig_464_);
if (v_isSharedCheck_542_ == 0)
{
v___x_505_ = v_buildConfig_464_;
v_isShared_506_ = v_isSharedCheck_542_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_macosxDeploymentTarget_x3f_503_);
lean_inc(v_leanOptOverrides_502_);
lean_inc(v_outputsFile_x3f_501_);
lean_inc(v_toLogConfig_494_);
lean_dec(v_buildConfig_464_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_542_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v_failLv_507_; uint8_t v_outLv_508_; uint8_t v_ansiMode_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_540_; 
v_failLv_507_ = lean_ctor_get_uint8(v_toLogConfig_494_, sizeof(void*)*1);
v_outLv_508_ = lean_ctor_get_uint8(v_toLogConfig_494_, sizeof(void*)*1 + 1);
v_ansiMode_509_ = lean_ctor_get_uint8(v_toLogConfig_494_, sizeof(void*)*1 + 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_toLogConfig_494_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v_toLogConfig_494_, 0);
lean_dec(v_unused_541_);
v___x_511_ = v_toLogConfig_494_;
v_isShared_512_ = v_isSharedCheck_540_;
goto v_resetjp_510_;
}
else
{
lean_dec(v_toLogConfig_494_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_540_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_513_, 0, v_fst_476_);
lean_ctor_set(v___x_513_, 1, v___y_484_);
lean_ctor_set(v___x_513_, 2, v___y_485_);
lean_inc(v___y_483_);
v___f_514_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0___boxed), 11, 4);
lean_closure_set(v___f_514_, 0, v_keyName_479_);
lean_closure_set(v___f_514_, 1, v___y_482_);
lean_closure_set(v___f_514_, 2, v___y_483_);
lean_closure_set(v___f_514_, 3, v___x_513_);
v___x_515_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_515_);
v___x_517_ = v___x_511_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, sizeof(void*)*1, v_failLv_507_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, sizeof(void*)*1 + 1, v_outLv_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, sizeof(void*)*1 + 2, v_ansiMode_509_);
v___x_517_ = v_reuseFailAlloc_539_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_517_);
v___x_519_ = v___x_505_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 4, 6);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_outputsFile_x3f_501_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_leanOptOverrides_502_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_macosxDeploymentTarget_x3f_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, sizeof(void*)*4, v_oldMode_495_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, sizeof(void*)*4 + 1, v_trustHash_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, sizeof(void*)*4 + 2, v_noBuild_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, sizeof(void*)*4 + 3, v_failFast_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, sizeof(void*)*4 + 4, v_verbosity_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_538_, sizeof(void*)*4 + 5, v_showSuccess_500_);
v___x_519_ = v_reuseFailAlloc_538_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
lean_inc(v_a_465_);
v___x_520_ = l_Lake_Workspace_runBuild___redArg(v_a_465_, v___f_514_, v___x_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_520_, 0);
lean_dec(v_unused_529_);
v___x_522_ = v___x_520_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_dec(v___x_520_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Lake_Package_test___boxed__const__1;
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_520_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_520_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
}
}
}
v___jp_543_:
{
uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_544_ = 0;
v___x_545_ = l_Lean_Name_toString(v_baseName_478_, v___x_544_);
v___x_546_ = ((lean_object*)(l_Lake_Package_test___closed__2));
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
v___x_548_ = lean_string_append(v___x_547_, v_snd_477_);
lean_dec(v_snd_477_);
v___x_549_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
v___x_551_ = lean_mk_io_user_error(v___x_550_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
v___jp_553_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc(v_snd_477_);
v___x_554_ = l_String_toName(v_snd_477_);
v___x_555_ = l_Lake_Package_findTargetDecl_x3f(v___x_554_, v_fst_476_);
lean_dec(v___x_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_inc(v_baseName_478_);
lean_dec(v_keyName_479_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec_ref(v_testDriverArgs_469_);
lean_dec_ref(v_buildConfig_464_);
lean_dec(v_args_463_);
goto v___jp_543_;
}
else
{
lean_object* v_val_556_; lean_object* v_name_557_; lean_object* v_kind_558_; lean_object* v_config_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_val_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_556_);
lean_dec_ref_known(v___x_555_, 1);
v_name_557_ = lean_ctor_get(v_val_556_, 1);
lean_inc(v_name_557_);
v_kind_558_ = lean_ctor_get(v_val_556_, 2);
lean_inc(v_kind_558_);
v_config_559_ = lean_ctor_get(v_val_556_, 3);
lean_inc(v_config_559_);
lean_dec(v_val_556_);
v___x_560_ = ((lean_object*)(l_Lake_Package_test___closed__4));
v___x_561_ = lean_name_eq(v_kind_558_, v___x_560_);
lean_dec(v_kind_558_);
if (v___x_561_ == 0)
{
lean_inc(v_baseName_478_);
lean_dec(v_config_559_);
lean_dec(v_name_557_);
lean_dec(v_keyName_479_);
lean_dec(v_fst_476_);
lean_del_object(v___x_474_);
lean_dec_ref(v_testDriverArgs_469_);
lean_dec_ref(v_buildConfig_464_);
lean_dec(v_args_463_);
goto v___jp_543_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
lean_dec(v_snd_477_);
v___x_562_ = lean_array_get_size(v_testDriverArgs_469_);
lean_dec_ref(v_testDriverArgs_469_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_nat_dec_eq(v___x_562_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec(v_args_463_);
lean_inc(v_name_557_);
v___y_482_ = v_name_557_;
v___y_483_ = v___x_560_;
v___y_484_ = v_name_557_;
v___y_485_ = v_config_559_;
v___y_486_ = v___x_564_;
goto v___jp_481_;
}
else
{
uint8_t v___x_565_; 
v___x_565_ = l_List_isEmpty___redArg(v_args_463_);
lean_dec(v_args_463_);
lean_inc(v_name_557_);
v___y_482_ = v_name_557_;
v___y_483_ = v___x_560_;
v___y_484_ = v_name_557_;
v___y_485_ = v_config_559_;
v___y_486_ = v___x_565_;
goto v___jp_481_;
}
}
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_testDriverArgs_469_);
lean_dec_ref(v_buildConfig_464_);
lean_dec(v_args_463_);
v_a_595_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_471_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_471_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed(lean_object* v_pkg_603_, lean_object* v_args_604_, lean_object* v_buildConfig_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lake_Package_test(v_pkg_603_, v_args_604_, v_buildConfig_605_, v_a_606_);
lean_dec(v_a_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object* v_pkg_611_, lean_object* v_args_612_, lean_object* v_buildConfig_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_config_616_; lean_object* v_lintDriver_617_; lean_object* v_lintDriverArgs_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_config_616_ = lean_ctor_get(v_pkg_611_, 6);
v_lintDriver_617_ = lean_ctor_get(v_pkg_611_, 23);
lean_inc_ref(v_lintDriver_617_);
v_lintDriverArgs_618_ = lean_ctor_get(v_config_616_, 15);
lean_inc_ref(v_lintDriverArgs_618_);
v___x_619_ = ((lean_object*)(l_Lake_Package_lint___closed__0));
v___x_620_ = l_Lake_Package_resolveDriver(v_pkg_611_, v___x_619_, v_lintDriver_617_, v_a_614_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_670_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_670_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_670_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_670_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v_baseName_627_; lean_object* v_keyName_628_; lean_object* v_scripts_629_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_fst_625_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_fst_625_);
v_snd_626_ = lean_ctor_get(v_a_621_, 1);
lean_inc_n(v_snd_626_, 2);
lean_dec(v_a_621_);
v_baseName_627_ = lean_ctor_get(v_fst_625_, 1);
v_keyName_628_ = lean_ctor_get(v_fst_625_, 2);
lean_inc(v_keyName_628_);
v_scripts_629_ = lean_ctor_get(v_fst_625_, 18);
v___x_642_ = l_String_toName(v_snd_626_);
v___x_643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_629_, v___x_642_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v___x_642_);
lean_dec(v_keyName_628_);
lean_dec(v_snd_626_);
lean_dec(v_fst_625_);
lean_del_object(v___x_623_);
lean_dec_ref(v_buildConfig_613_);
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = lean_array_to_list(v_lintDriverArgs_618_);
v___x_646_ = l_List_appendTR___redArg(v___x_645_, v_args_612_);
v___x_647_ = l_Lake_Script_run(v___x_646_, v_val_644_, v_a_614_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; 
lean_dec(v___x_643_);
v___x_648_ = l_Lake_Package_findTargetDecl_x3f(v___x_642_, v_fst_625_);
lean_dec(v___x_642_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_inc(v_baseName_627_);
lean_dec(v_keyName_628_);
lean_dec(v_fst_625_);
lean_dec_ref(v_lintDriverArgs_618_);
lean_dec_ref(v_buildConfig_613_);
lean_dec(v_args_612_);
goto v___jp_630_;
}
else
{
lean_object* v_val_649_; lean_object* v_name_650_; lean_object* v_kind_651_; lean_object* v_config_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v___x_648_, 1);
v_name_650_ = lean_ctor_get(v_val_649_, 1);
lean_inc(v_name_650_);
v_kind_651_ = lean_ctor_get(v_val_649_, 2);
lean_inc(v_kind_651_);
v_config_652_ = lean_ctor_get(v_val_649_, 3);
lean_inc(v_config_652_);
lean_dec(v_val_649_);
v___x_653_ = l_Lake_LeanExe_keyword;
v___x_654_ = lean_name_eq(v_kind_651_, v___x_653_);
lean_dec(v_kind_651_);
if (v___x_654_ == 0)
{
lean_inc(v_baseName_627_);
lean_dec(v_config_652_);
lean_dec(v_name_650_);
lean_dec(v_keyName_628_);
lean_dec(v_fst_625_);
lean_dec_ref(v_lintDriverArgs_618_);
lean_dec_ref(v_buildConfig_613_);
lean_dec(v_args_612_);
goto v___jp_630_;
}
else
{
lean_object* v___x_655_; lean_object* v___f_656_; lean_object* v___x_657_; 
lean_dec(v_snd_626_);
lean_del_object(v___x_623_);
lean_inc(v_name_650_);
v___x_655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_655_, 0, v_fst_625_);
lean_ctor_set(v___x_655_, 1, v_name_650_);
lean_ctor_set(v___x_655_, 2, v_config_652_);
v___f_656_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_656_, 0, v_keyName_628_);
lean_closure_set(v___f_656_, 1, v_name_650_);
lean_closure_set(v___f_656_, 2, v___x_653_);
lean_closure_set(v___f_656_, 3, v___x_655_);
lean_inc(v_a_614_);
v___x_657_ = l_Lake_Workspace_runBuild___redArg(v_a_614_, v___f_656_, v_buildConfig_613_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_array_mk(v_args_612_);
v___x_660_ = l_Array_append___redArg(v_lintDriverArgs_618_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = l_Lake_env(v_a_658_, v___x_660_, v_a_614_);
return v___x_661_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_lintDriverArgs_618_);
lean_dec(v_args_612_);
v_a_662_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_657_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_657_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
v___jp_630_:
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_631_ = 0;
v___x_632_ = l_Lean_Name_toString(v_baseName_627_, v___x_631_);
v___x_633_ = ((lean_object*)(l_Lake_Package_lint___closed__1));
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
v___x_635_ = lean_string_append(v___x_634_, v_snd_626_);
lean_dec(v_snd_626_);
v___x_636_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
v___x_638_ = lean_mk_io_user_error(v___x_637_);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 1);
lean_ctor_set(v___x_623_, 0, v___x_638_);
v___x_640_ = v___x_623_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_lintDriverArgs_618_);
lean_dec_ref(v_buildConfig_613_);
lean_dec(v_args_612_);
v_a_671_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_620_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_620_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint___boxed(lean_object* v_pkg_679_, lean_object* v_args_680_, lean_object* v_buildConfig_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lake_Package_lint(v_pkg_679_, v_args_680_, v_buildConfig_681_, v_a_682_);
lean_dec(v_a_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object* v_ws_685_, lean_object* v_leanFile_686_, lean_object* v_moreArgs_687_, lean_object* v_buildConfig_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_closure((void*)(l_Lake_prepareLeanCommand___boxed), 9, 2);
lean_closure_set(v___x_690_, 0, v_leanFile_686_);
lean_closure_set(v___x_690_, 1, v_moreArgs_687_);
v___x_691_ = l_Lake_Workspace_runBuild___redArg(v_ws_685_, v___x_690_, v_buildConfig_688_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_n(v_a_692_, 2);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = lean_io_process_spawn(v_a_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v_toStdioConfig_695_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v_toStdioConfig_695_ = lean_ctor_get(v_a_692_, 0);
lean_inc_ref(v_toStdioConfig_695_);
lean_dec(v_a_692_);
v___x_696_ = lean_io_process_child_wait(v_toStdioConfig_695_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_toStdioConfig_695_);
return v___x_696_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_a_692_);
v_a_697_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_693_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
v_a_705_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_691_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_691_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile___boxed(lean_object* v_ws_713_, lean_object* v_leanFile_714_, lean_object* v_moreArgs_715_, lean_object* v_buildConfig_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lake_Workspace_evalLeanFile(v_ws_713_, v_leanFile_714_, v_moreArgs_715_, v_buildConfig_716_);
return v_res_718_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Run(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Module(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Targets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Package_test___boxed__const__1 = _init_l_Lake_Package_test___boxed__const__1();
lean_mark_persistent(l_Lake_Package_test___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Actions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Build_Run(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* initialize_Lake_Build_Module(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Actions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Actions(builtin);
}
#ifdef __cplusplus
}
#endif
