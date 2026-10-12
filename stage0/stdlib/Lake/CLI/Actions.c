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
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Package_test___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = ": invalid test driver: unknown script, executable, or library '"};
static const lean_object* l_Lake_Package_test___closed__1 = (const lean_object*)&l_Lake_Package_test___closed__1_value;
static const lean_string_object l_Lake_Package_test___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = ": arguments cannot be passed to a library test driver"};
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
lean_object* l_Lake_env(lean_object* v_cmd_3_, lean_object* v_args_4_, lean_object* v_a_5_){
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
LEAN_EXPORT void l_Lake_env_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_3_ = stack[0].m_obj;
lean_object* v_args_4_ = stack[1].m_obj;
lean_object* v_a_5_ = stack[2].m_obj;
lean_object* v_res_24_;
v_res_24_ = l_Lake_env(v_cmd_3_, v_args_4_, v_a_5_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lake_env___boxed(lean_object* v_cmd_25_, lean_object* v_args_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_env(v_cmd_25_, v_args_26_, v_a_27_);
lean_dec(v_a_27_);
return v_res_29_;
}
}
lean_object* l_Lake_exe___lam__0(lean_object* v_val_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_pkg_38_; lean_object* v_name_39_; lean_object* v_keyName_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_pkg_38_ = lean_ctor_get(v_val_30_, 0);
v_name_39_ = lean_ctor_get(v_val_30_, 1);
v_keyName_40_ = lean_ctor_get(v_pkg_38_, 2);
v___x_41_ = l_Lake_LeanExe_exeFacet;
lean_inc(v_name_39_);
lean_inc(v_keyName_40_);
v___x_42_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_42_, 0, v_keyName_40_);
lean_ctor_set(v___x_42_, 1, v_name_39_);
v___x_43_ = l_Lake_LeanExe_keyword;
v___x_44_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
lean_ctor_set(v___x_44_, 2, v_val_30_);
lean_ctor_set(v___x_44_, 3, v___x_41_);
v___x_45_ = lean_apply_7(v___y_31_, v___x_44_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT void l_Lake_exe___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_30_ = stack[0].m_obj;
lean_object* v___y_31_ = stack[1].m_obj;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v___y_33_ = stack[3].m_obj;
lean_object* v___y_34_ = stack[4].m_obj;
lean_object* v___y_35_ = stack[5].m_obj;
lean_object* v___y_36_ = stack[6].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lake_exe___lam__0(v_val_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object* v_val_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lake_exe___lam__0(v_val_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
return v_res_55_;
}
}
lean_object* l_Lake_exe(lean_object* v_name_58_, lean_object* v_args_59_, lean_object* v_buildConfig_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lake_Workspace_findLeanExe_x3f(v_name_58_, v_a_61_);
if (lean_obj_tag(v___x_63_) == 1)
{
lean_object* v_val_64_; lean_object* v___f_65_; lean_object* v___x_66_; 
lean_dec(v_name_58_);
v_val_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v___x_63_, 1);
v___f_65_ = lean_alloc_closure((void*)(l_Lake_exe___lam__0___boxed), 8, 1);
lean_closure_set(v___f_65_, 0, v_val_64_);
lean_inc(v_a_61_);
v___x_66_ = l_Lake_Workspace_runBuild___redArg(v_a_61_, v___f_65_, v_buildConfig_60_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_68_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = l_Lake_env(v_a_67_, v_args_59_, v_a_61_);
return v___x_68_;
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
lean_dec_ref(v_args_59_);
v_a_69_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_66_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_66_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
else
{
lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v___x_63_);
lean_dec_ref(v_buildConfig_60_);
lean_dec_ref(v_args_59_);
v___x_77_ = ((lean_object*)(l_Lake_exe___closed__0));
v___x_78_ = 1;
v___x_79_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_58_, v___x_78_);
v___x_80_ = lean_string_append(v___x_77_, v___x_79_);
lean_dec_ref(v___x_79_);
v___x_81_ = ((lean_object*)(l_Lake_exe___closed__1));
v___x_82_ = lean_string_append(v___x_80_, v___x_81_);
v___x_83_ = lean_mk_io_user_error(v___x_82_);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT void l_Lake_exe_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_58_ = stack[0].m_obj;
lean_object* v_args_59_ = stack[1].m_obj;
lean_object* v_buildConfig_60_ = stack[2].m_obj;
lean_object* v_a_61_ = stack[3].m_obj;
lean_object* v_res_85_;
v_res_85_ = l_Lake_exe(v_name_58_, v_args_59_, v_buildConfig_60_, v_a_61_);
stack->m_obj
 = v_res_85_;
}
LEAN_EXPORT lean_object* l_Lake_exe___boxed(lean_object* v_name_86_, lean_object* v_args_87_, lean_object* v_buildConfig_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lake_exe(v_name_86_, v_args_87_, v_buildConfig_88_, v_a_89_);
lean_dec(v_a_89_);
return v_res_91_;
}
}
lean_object* l_Lake_Package_pack(lean_object* v_pkg_95_, lean_object* v_file_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_config_99_; lean_object* v_dir_100_; lean_object* v_buildDir_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_config_99_ = lean_ctor_get(v_pkg_95_, 6);
lean_inc_ref(v_config_99_);
v_dir_100_ = lean_ctor_get(v_pkg_95_, 4);
lean_inc_ref(v_dir_100_);
lean_dec_ref(v_pkg_95_);
v_buildDir_101_ = lean_ctor_get(v_config_99_, 5);
lean_inc_ref(v_buildDir_101_);
lean_dec_ref(v_config_99_);
v___x_102_ = ((lean_object*)(l_Lake_Package_pack___closed__0));
v___x_103_ = lean_string_append(v___x_102_, v_file_96_);
v___x_104_ = 1;
v___x_105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*1, v___x_104_);
v___x_106_ = lean_array_push(v_a_97_, v___x_105_);
v___x_107_ = l_System_FilePath_normalize(v_buildDir_101_);
v___x_108_ = l_Lake_joinRelative(v_dir_100_, v___x_107_);
v___x_109_ = 1;
v___x_110_ = ((lean_object*)(l_Lake_Package_pack___closed__1));
v___x_111_ = l_Lake_tar(v___x_108_, v_file_96_, v___x_109_, v___x_110_, v___x_106_);
return v___x_111_;
}
}
LEAN_EXPORT void l_Lake_Package_pack_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_95_ = stack[0].m_obj;
lean_object* v_file_96_ = stack[1].m_obj;
lean_object* v_a_97_ = stack[2].m_obj;
lean_object* v_res_112_;
v_res_112_ = l_Lake_Package_pack(v_pkg_95_, v_file_96_, v_a_97_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lake_Package_pack___boxed(lean_object* v_pkg_113_, lean_object* v_file_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lake_Package_pack(v_pkg_113_, v_file_114_, v_a_115_);
return v_res_117_;
}
}
lean_object* l_Lake_Package_unpack(lean_object* v_pkg_119_, lean_object* v_file_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_config_123_; lean_object* v_dir_124_; lean_object* v_buildDir_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; 
v_config_123_ = lean_ctor_get(v_pkg_119_, 6);
lean_inc_ref(v_config_123_);
v_dir_124_ = lean_ctor_get(v_pkg_119_, 4);
lean_inc_ref(v_dir_124_);
lean_dec_ref(v_pkg_119_);
v_buildDir_125_ = lean_ctor_get(v_config_123_, 5);
lean_inc_ref(v_buildDir_125_);
lean_dec_ref(v_config_123_);
v___x_126_ = ((lean_object*)(l_Lake_Package_unpack___closed__0));
v___x_127_ = lean_string_append(v___x_126_, v_file_120_);
v___x_128_ = 1;
v___x_129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = lean_array_push(v_a_121_, v___x_129_);
v___x_131_ = l_System_FilePath_normalize(v_buildDir_125_);
v___x_132_ = l_Lake_joinRelative(v_dir_124_, v___x_131_);
v___x_133_ = 1;
v___x_134_ = l_Lake_untar(v_file_120_, v___x_132_, v___x_133_, v___x_130_);
return v___x_134_;
}
}
LEAN_EXPORT void l_Lake_Package_unpack_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_119_ = stack[0].m_obj;
lean_object* v_file_120_ = stack[1].m_obj;
lean_object* v_a_121_ = stack[2].m_obj;
lean_object* v_res_135_;
v_res_135_ = l_Lake_Package_unpack(v_pkg_119_, v_file_120_, v_a_121_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_Lake_Package_unpack___boxed(lean_object* v_pkg_136_, lean_object* v_file_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lake_Package_unpack(v_pkg_136_, v_file_137_, v_a_138_);
return v_res_140_;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__7(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__4));
v___x_150_ = lean_unsigned_to_nat(5u);
v___x_151_ = lean_mk_empty_array_with_capacity(v___x_150_);
v___x_152_ = lean_array_push(v___x_151_, v___x_149_);
return v___x_152_;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__8(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__5));
v___x_154_ = lean_obj_once(&l_Lake_Package_uploadRelease___closed__7, &l_Lake_Package_uploadRelease___closed__7_once, _init_l_Lake_Package_uploadRelease___closed__7);
v___x_155_ = lean_array_push(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Lake_Package_uploadRelease___closed__10(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__9));
v___x_158_ = lean_unsigned_to_nat(2u);
v___x_159_ = lean_mk_empty_array_with_capacity(v___x_158_);
v___x_160_ = lean_array_push(v___x_159_, v___x_157_);
return v___x_160_;
}
}
lean_object* l_Lake_Package_uploadRelease(lean_object* v_pkg_161_, lean_object* v_tag_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_args_166_; lean_object* v___y_167_; lean_object* v_dir_176_; lean_object* v_config_177_; lean_object* v_buildArchive_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_dir_176_ = lean_ctor_get(v_pkg_161_, 4);
v_config_177_ = lean_ctor_get(v_pkg_161_, 6);
lean_inc_ref(v_config_177_);
v_buildArchive_178_ = lean_ctor_get(v_pkg_161_, 21);
lean_inc_ref_n(v_buildArchive_178_, 2);
v___x_179_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_176_);
v___x_180_ = l_Lake_joinRelative(v_dir_176_, v___x_179_);
v___x_181_ = l_Lake_joinRelative(v___x_180_, v_buildArchive_178_);
lean_inc_ref(v___x_181_);
v___x_182_ = l_Lake_Package_pack(v_pkg_161_, v___x_181_, v_a_163_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v_releaseRepo_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_a_183_ = lean_ctor_get(v___x_182_, 1);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 2);
v_releaseRepo_184_ = lean_ctor_get(v_config_177_, 10);
lean_inc(v_releaseRepo_184_);
lean_dec_ref(v_config_177_);
v___x_185_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__2));
v___x_186_ = lean_string_append(v___x_185_, v_tag_162_);
v___x_187_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__3));
v___x_188_ = lean_string_append(v___x_186_, v___x_187_);
v___x_189_ = lean_string_append(v___x_188_, v_buildArchive_178_);
lean_dec_ref(v_buildArchive_178_);
v___x_190_ = 1;
v___x_191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_190_);
v___x_192_ = lean_array_push(v_a_183_, v___x_191_);
v___x_193_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__6));
v___x_194_ = lean_obj_once(&l_Lake_Package_uploadRelease___closed__8, &l_Lake_Package_uploadRelease___closed__8_once, _init_l_Lake_Package_uploadRelease___closed__8);
v___x_195_ = lean_array_push(v___x_194_, v_tag_162_);
v___x_196_ = lean_array_push(v___x_195_, v___x_181_);
v___x_197_ = lean_array_push(v___x_196_, v___x_193_);
if (lean_obj_tag(v_releaseRepo_184_) == 1)
{
lean_object* v_val_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_val_198_ = lean_ctor_get(v_releaseRepo_184_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v_releaseRepo_184_, 1);
v___x_199_ = lean_obj_once(&l_Lake_Package_uploadRelease___closed__10, &l_Lake_Package_uploadRelease___closed__10_once, _init_l_Lake_Package_uploadRelease___closed__10);
v___x_200_ = lean_array_push(v___x_199_, v_val_198_);
v___x_201_ = l_Array_append___redArg(v___x_197_, v___x_200_);
lean_dec_ref(v___x_200_);
v_args_166_ = v___x_201_;
v___y_167_ = v___x_192_;
goto v___jp_165_;
}
else
{
lean_dec(v_releaseRepo_184_);
v_args_166_ = v___x_197_;
v___y_167_ = v___x_192_;
goto v___jp_165_;
}
}
else
{
lean_dec_ref(v___x_181_);
lean_dec_ref(v_buildArchive_178_);
lean_dec_ref(v_config_177_);
lean_dec_ref(v_tag_162_);
return v___x_182_;
}
v___jp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_168_ = ((lean_object*)(l_Lake_env___closed__0));
v___x_169_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__0));
v___x_170_ = lean_box(0);
v___x_171_ = ((lean_object*)(l_Lake_Package_uploadRelease___closed__1));
v___x_172_ = 1;
v___x_173_ = 0;
v___x_174_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_174_, 0, v___x_168_);
lean_ctor_set(v___x_174_, 1, v___x_169_);
lean_ctor_set(v___x_174_, 2, v_args_166_);
lean_ctor_set(v___x_174_, 3, v___x_170_);
lean_ctor_set(v___x_174_, 4, v___x_171_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*5, v___x_172_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*5 + 1, v___x_173_);
v___x_175_ = l_Lake_proc(v___x_174_, v___x_173_, v___x_170_, v___y_167_);
return v___x_175_;
}
}
}
LEAN_EXPORT void l_Lake_Package_uploadRelease_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_161_ = stack[0].m_obj;
lean_object* v_tag_162_ = stack[1].m_obj;
lean_object* v_a_163_ = stack[2].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lake_Package_uploadRelease(v_pkg_161_, v_tag_162_, v_a_163_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease___boxed(lean_object* v_pkg_203_, lean_object* v_tag_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lake_Package_uploadRelease(v_pkg_203_, v_tag_204_, v_a_205_);
return v_res_207_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg(){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___closed__0));
return v___x_211_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_212_;
v_res_212_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg();
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg___boxed(lean_object* v___dummy_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg();
return v_res_214_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___redArg();
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(lean_object* v_s_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___boxed(lean_object* v_s_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(v_s_218_);
lean_dec_ref(v_s_218_);
return v_res_219_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(lean_object* v___x_223_, lean_object* v_as_224_, size_t v_sz_225_, size_t v_i_226_, lean_object* v_b_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_lt(v_i_226_, v_sz_225_);
if (v___x_228_ == 0)
{
lean_inc_ref(v_b_227_);
return v_b_227_;
}
else
{
lean_object* v_a_229_; lean_object* v_baseName_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_a_229_ = lean_array_uget_borrowed(v_as_224_, v_i_226_);
v_baseName_230_ = lean_ctor_get(v_a_229_, 1);
v___x_231_ = lean_box(0);
v___x_232_ = lean_name_eq(v_baseName_230_, v___x_223_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; size_t v___x_234_; size_t v___x_235_; 
v___x_233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0));
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_226_, v___x_234_);
v_i_226_ = v___x_235_;
v_b_227_ = v___x_233_;
goto _start;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_inc(v_a_229_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v_a_229_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_231_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_223_ = stack[0].m_obj;
lean_object* v_as_224_ = stack[1].m_obj;
size_t v_sz_225_ = stack[2].m_num;
size_t v_i_226_ = stack[3].m_num;
lean_object* v_b_227_ = stack[4].m_obj;
lean_object* v_res_240_;
v_res_240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_223_, v_as_224_, v_sz_225_, v_i_226_, v_b_227_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___boxed(lean_object* v___x_241_, lean_object* v_as_242_, lean_object* v_sz_243_, lean_object* v_i_244_, lean_object* v_b_245_){
_start:
{
size_t v_sz_boxed_246_; size_t v_i_boxed_247_; lean_object* v_res_248_; 
v_sz_boxed_246_ = lean_unbox_usize(v_sz_243_);
lean_dec(v_sz_243_);
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_241_, v_as_242_, v_sz_boxed_246_, v_i_boxed_247_, v_b_245_);
lean_dec_ref(v_b_245_);
lean_dec_ref(v_as_242_);
lean_dec(v___x_241_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(lean_object* v_driver_249_, lean_object* v___x_250_, lean_object* v___x_251_, lean_object* v_a_252_, lean_object* v_b_253_){
_start:
{
lean_object* v_it_255_; lean_object* v_startInclusive_256_; lean_object* v_endExclusive_257_; 
if (lean_obj_tag(v_a_252_) == 0)
{
lean_object* v_currPos_262_; lean_object* v_searcher_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_286_; 
v_currPos_262_ = lean_ctor_get(v_a_252_, 0);
v_searcher_263_ = lean_ctor_get(v_a_252_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_286_ == 0)
{
v___x_265_ = v_a_252_;
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_searcher_263_);
lean_inc(v_currPos_262_);
lean_dec(v_a_252_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_286_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
uint8_t v_decide_267_; 
v_decide_267_ = lean_nat_dec_eq(v_searcher_263_, v___x_251_);
if (v_decide_267_ == 0)
{
uint32_t v___x_268_; uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_268_ = 47;
v___x_269_ = lean_string_utf8_get_fast(v_driver_249_, v_searcher_263_);
v___x_270_ = lean_uint32_dec_eq(v___x_269_, v___x_268_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = lean_string_utf8_next_fast(v_driver_249_, v_searcher_263_);
lean_dec(v_searcher_263_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_271_);
v___x_273_ = v___x_265_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_currPos_262_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_275_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
v_a_252_ = v___x_273_;
goto _start;
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_slice_279_; lean_object* v_nextIt_281_; 
v___x_276_ = lean_string_utf8_next_fast(v_driver_249_, v_searcher_263_);
v___x_277_ = lean_nat_sub(v___x_276_, v_searcher_263_);
v___x_278_ = lean_nat_add(v_searcher_263_, v___x_277_);
lean_dec(v___x_277_);
v_slice_279_ = l_String_Slice_subslice_x21(v___x_250_, v_currPos_262_, v_searcher_263_);
lean_inc(v___x_278_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_278_);
lean_ctor_set(v___x_265_, 0, v___x_278_);
v_nextIt_281_ = v___x_265_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___x_278_);
v_nextIt_281_ = v_reuseFailAlloc_284_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v_startInclusive_282_; lean_object* v_endExclusive_283_; 
v_startInclusive_282_ = lean_ctor_get(v_slice_279_, 0);
lean_inc(v_startInclusive_282_);
v_endExclusive_283_ = lean_ctor_get(v_slice_279_, 1);
lean_inc(v_endExclusive_283_);
lean_dec_ref(v_slice_279_);
v_it_255_ = v_nextIt_281_;
v_startInclusive_256_ = v_startInclusive_282_;
v_endExclusive_257_ = v_endExclusive_283_;
goto v___jp_254_;
}
}
}
else
{
lean_object* v___x_285_; 
lean_del_object(v___x_265_);
lean_dec(v_searcher_263_);
v___x_285_ = lean_box(1);
lean_inc(v___x_251_);
v_it_255_ = v___x_285_;
v_startInclusive_256_ = v_currPos_262_;
v_endExclusive_257_ = v___x_251_;
goto v___jp_254_;
}
}
}
else
{
lean_dec(v___x_251_);
lean_dec_ref(v_driver_249_);
return v_b_253_;
}
v___jp_254_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_inc_ref(v_driver_249_);
v___x_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_258_, 0, v_driver_249_);
lean_ctor_set(v___x_258_, 1, v_startInclusive_256_);
lean_ctor_set(v___x_258_, 2, v_endExclusive_257_);
v___x_259_ = l_String_Slice_toString(v___x_258_);
lean_dec_ref_known(v___x_258_, 3);
v___x_260_ = lean_array_push(v_b_253_, v___x_259_);
v_a_252_ = v_it_255_;
v_b_253_ = v___x_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object* v_driver_287_, lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v_a_290_, lean_object* v_b_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_287_, v___x_288_, v___x_289_, v_a_290_, v_b_291_);
lean_dec_ref(v___x_288_);
return v_res_292_;
}
}
lean_object* l_Lake_Package_resolveDriver(lean_object* v_pkg_301_, lean_object* v_kind_302_, lean_object* v_driver_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = lean_string_utf8_byte_size(v_driver_303_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_nat_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_inc_ref_n(v_driver_303_, 2);
v___x_322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_322_, 0, v_driver_303_);
lean_ctor_set(v___x_322_, 1, v___x_307_);
lean_ctor_set(v___x_322_, 2, v___x_306_);
v___x_323_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0);
v___x_324_ = ((lean_object*)(l_Lake_Package_pack___closed__1));
v___x_325_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_303_, v___x_322_, v___x_306_, v___x_323_, v___x_324_);
lean_dec_ref_known(v___x_322_, 3);
v___x_326_ = lean_array_to_list(v___x_325_);
if (lean_obj_tag(v___x_326_) == 1)
{
lean_object* v_head_327_; lean_object* v_tail_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_375_; 
v_head_327_ = lean_ctor_get(v___x_326_, 0);
v_tail_328_ = lean_ctor_get(v___x_326_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_375_ == 0)
{
v___x_330_ = v___x_326_;
v_isShared_331_ = v_isSharedCheck_375_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_tail_328_);
lean_inc(v_head_327_);
lean_dec(v___x_326_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_375_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
if (lean_obj_tag(v_tail_328_) == 0)
{
lean_object* v___x_346_; 
lean_dec_ref(v_driver_303_);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 0);
lean_ctor_set(v___x_330_, 1, v_head_327_);
lean_ctor_set(v___x_330_, 0, v_pkg_301_);
v___x_346_ = v___x_330_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_pkg_301_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_head_327_);
v___x_346_ = v_reuseFailAlloc_348_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
else
{
lean_object* v_tail_349_; 
lean_del_object(v___x_330_);
v_tail_349_ = lean_ctor_get(v_tail_328_, 1);
if (lean_obj_tag(v_tail_349_) == 0)
{
lean_object* v_head_350_; lean_object* v_packages_351_; lean_object* v___x_352_; lean_object* v___x_353_; size_t v_sz_354_; size_t v___x_355_; lean_object* v___x_356_; lean_object* v_fst_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_driver_303_);
v_head_350_ = lean_ctor_get(v_tail_328_, 0);
lean_inc(v_head_350_);
lean_dec_ref_known(v_tail_328_, 2);
v_packages_351_ = lean_ctor_get(v_a_304_, 4);
lean_inc(v_head_327_);
v___x_352_ = l_String_toName(v_head_327_);
v___x_353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0));
v_sz_354_ = lean_array_size(v_packages_351_);
v___x_355_ = ((size_t)0ULL);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_352_, v_packages_351_, v_sz_354_, v___x_355_, v___x_353_);
lean_dec(v___x_352_);
v_fst_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_356_, 1);
lean_dec(v_unused_374_);
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_fst_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
if (lean_obj_tag(v_fst_357_) == 0)
{
lean_del_object(v___x_359_);
lean_dec(v_head_350_);
goto v___jp_332_;
}
else
{
lean_object* v_val_361_; 
v_val_361_ = lean_ctor_get(v_fst_357_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v_fst_357_, 1);
if (lean_obj_tag(v_val_361_) == 1)
{
lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_372_; 
lean_dec(v_head_327_);
lean_dec_ref(v_pkg_301_);
v_val_362_ = lean_ctor_get(v_val_361_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_val_361_);
if (v_isSharedCheck_372_ == 0)
{
v___x_364_ = v_val_361_;
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_dec(v_val_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_head_350_);
lean_ctor_set(v___x_359_, 0, v_val_362_);
v___x_367_ = v___x_359_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_val_362_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_head_350_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 0);
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
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
else
{
lean_dec(v_val_361_);
lean_del_object(v___x_359_);
lean_dec(v_head_350_);
goto v___jp_332_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_328_, 2);
lean_dec(v_head_327_);
goto v___jp_309_;
}
}
v___jp_332_:
{
lean_object* v_baseName_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_baseName_333_ = lean_ctor_get(v_pkg_301_, 1);
lean_inc(v_baseName_333_);
lean_dec_ref(v_pkg_301_);
v___x_334_ = l_Lean_Name_toString(v_baseName_333_, v___x_308_);
v___x_335_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__3));
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
v___x_337_ = lean_string_append(v___x_336_, v_kind_302_);
v___x_338_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__4));
v___x_339_ = lean_string_append(v___x_337_, v___x_338_);
v___x_340_ = lean_string_append(v___x_339_, v_head_327_);
lean_dec(v_head_327_);
v___x_341_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_342_ = lean_string_append(v___x_340_, v___x_341_);
v___x_343_ = lean_mk_io_user_error(v___x_342_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
}
else
{
lean_dec(v___x_326_);
goto v___jp_309_;
}
}
else
{
lean_object* v_baseName_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec_ref(v_driver_303_);
v_baseName_376_ = lean_ctor_get(v_pkg_301_, 1);
lean_inc(v_baseName_376_);
lean_dec_ref(v_pkg_301_);
v___x_377_ = 0;
v___x_378_ = l_Lean_Name_toString(v_baseName_376_, v___x_377_);
v___x_379_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__6));
v___x_380_ = lean_string_append(v___x_378_, v___x_379_);
v___x_381_ = lean_string_append(v___x_380_, v_kind_302_);
v___x_382_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__7));
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
v___x_384_ = lean_mk_io_user_error(v___x_383_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
v___jp_309_:
{
lean_object* v_baseName_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_baseName_310_ = lean_ctor_get(v_pkg_301_, 1);
lean_inc(v_baseName_310_);
lean_dec_ref(v_pkg_301_);
v___x_311_ = l_Lean_Name_toString(v_baseName_310_, v___x_308_);
v___x_312_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__0));
v___x_313_ = lean_string_append(v___x_311_, v___x_312_);
v___x_314_ = lean_string_append(v___x_313_, v_kind_302_);
v___x_315_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__1));
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
v___x_317_ = lean_string_append(v___x_316_, v_driver_303_);
lean_dec_ref(v_driver_303_);
v___x_318_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__2));
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
v___x_320_ = lean_mk_io_user_error(v___x_319_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
}
LEAN_EXPORT void l_Lake_Package_resolveDriver_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_301_ = stack[0].m_obj;
lean_object* v_kind_302_ = stack[1].m_obj;
lean_object* v_driver_303_ = stack[2].m_obj;
lean_object* v_a_304_ = stack[3].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lake_Package_resolveDriver(v_pkg_301_, v_kind_302_, v_driver_303_, v_a_304_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object* v_pkg_387_, lean_object* v_kind_388_, lean_object* v_driver_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lake_Package_resolveDriver(v_pkg_387_, v_kind_388_, v_driver_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_kind_388_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(lean_object* v_driver_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v_inst_396_, lean_object* v_R_397_, lean_object* v_a_398_, lean_object* v_b_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_393_, v___x_394_, v___x_395_, v_a_398_, v_b_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___boxed(lean_object* v_driver_401_, lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v_inst_404_, lean_object* v_R_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(v_driver_401_, v___x_402_, v___x_403_, v_inst_404_, v_R_405_, v_a_406_, v_b_407_);
lean_dec_ref(v___x_402_);
return v_res_408_;
}
}
lean_object* l_Lake_Package_test___lam__0(lean_object* v_keyName_409_, lean_object* v_name_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = l_Lake_LeanLib_defaultFacet;
v___x_421_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_421_, 0, v_keyName_409_);
lean_ctor_set(v___x_421_, 1, v_name_410_);
v___x_422_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_411_);
lean_ctor_set(v___x_422_, 2, v___x_412_);
lean_ctor_set(v___x_422_, 3, v___x_420_);
v___x_423_ = lean_apply_7(v___y_413_, v___x_422_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, lean_box(0));
return v___x_423_;
}
}
LEAN_EXPORT void l_Lake_Package_test___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_keyName_409_ = stack[0].m_obj;
lean_object* v_name_410_ = stack[1].m_obj;
lean_object* v___x_411_ = stack[2].m_obj;
lean_object* v___x_412_ = stack[3].m_obj;
lean_object* v___y_413_ = stack[4].m_obj;
lean_object* v___y_414_ = stack[5].m_obj;
lean_object* v___y_415_ = stack[6].m_obj;
lean_object* v___y_416_ = stack[7].m_obj;
lean_object* v___y_417_ = stack[8].m_obj;
lean_object* v___y_418_ = stack[9].m_obj;
lean_object* v_res_424_;
v_res_424_ = l_Lake_Package_test___lam__0(v_keyName_409_, v_name_410_, v___x_411_, v___x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0___boxed(lean_object* v_keyName_425_, lean_object* v_name_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lake_Package_test___lam__0(v_keyName_425_, v_name_426_, v___x_427_, v___x_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v_res_436_;
}
}
lean_object* l_Lake_Package_test___lam__1(lean_object* v_keyName_437_, lean_object* v_name_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = l_Lake_LeanExe_exeFacet;
v___x_449_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_449_, 0, v_keyName_437_);
lean_ctor_set(v___x_449_, 1, v_name_438_);
v___x_450_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_439_);
lean_ctor_set(v___x_450_, 2, v___x_440_);
lean_ctor_set(v___x_450_, 3, v___x_448_);
v___x_451_ = lean_apply_7(v___y_441_, v___x_450_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, lean_box(0));
return v___x_451_;
}
}
LEAN_EXPORT void l_Lake_Package_test___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keyName_437_ = stack[0].m_obj;
lean_object* v_name_438_ = stack[1].m_obj;
lean_object* v___x_439_ = stack[2].m_obj;
lean_object* v___x_440_ = stack[3].m_obj;
lean_object* v___y_441_ = stack[4].m_obj;
lean_object* v___y_442_ = stack[5].m_obj;
lean_object* v___y_443_ = stack[6].m_obj;
lean_object* v___y_444_ = stack[7].m_obj;
lean_object* v___y_445_ = stack[8].m_obj;
lean_object* v___y_446_ = stack[9].m_obj;
lean_object* v_res_452_;
v_res_452_ = l_Lake_Package_test___lam__1(v_keyName_437_, v_name_438_, v___x_439_, v___x_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1___boxed(lean_object* v_keyName_453_, lean_object* v_name_454_, lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lake_Package_test___lam__1(v_keyName_453_, v_name_454_, v___x_455_, v___x_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
return v_res_464_;
}
}
static lean_object* _init_l_Lake_Package_test___boxed__const__1(void){
_start:
{
uint32_t v___x_471_; lean_object* v___x_472_; 
v___x_471_ = 0;
v___x_472_ = lean_box_uint32(v___x_471_);
return v___x_472_;
}
}
lean_object* l_Lake_Package_test(lean_object* v_pkg_473_, lean_object* v_args_474_, lean_object* v_buildConfig_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_config_478_; lean_object* v_testDriver_479_; lean_object* v_testDriverArgs_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_config_478_ = lean_ctor_get(v_pkg_473_, 6);
v_testDriver_479_ = lean_ctor_get(v_pkg_473_, 22);
lean_inc_ref(v_testDriver_479_);
v_testDriverArgs_480_ = lean_ctor_get(v_config_478_, 13);
lean_inc_ref(v_testDriverArgs_480_);
v___x_481_ = ((lean_object*)(l_Lake_Package_test___closed__0));
v___x_482_ = l_Lake_Package_resolveDriver(v_pkg_473_, v___x_481_, v_testDriver_479_, v_a_476_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_602_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_602_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_602_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_602_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v_baseName_489_; lean_object* v_keyName_490_; lean_object* v_scripts_491_; uint8_t v___y_505_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_fst_487_ = lean_ctor_get(v_a_483_, 0);
lean_inc(v_fst_487_);
v_snd_488_ = lean_ctor_get(v_a_483_, 1);
lean_inc_n(v_snd_488_, 2);
lean_dec(v_a_483_);
v_baseName_489_ = lean_ctor_get(v_fst_487_, 1);
v_keyName_490_ = lean_ctor_get(v_fst_487_, 2);
lean_inc(v_keyName_490_);
v_scripts_491_ = lean_ctor_get(v_fst_487_, 18);
v___x_574_ = l_String_toName(v_snd_488_);
v___x_575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_491_, v___x_574_);
if (lean_obj_tag(v___x_575_) == 1)
{
lean_object* v_val_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_574_);
lean_dec(v_keyName_490_);
lean_dec(v_snd_488_);
lean_dec(v_fst_487_);
lean_del_object(v___x_485_);
lean_dec_ref(v_buildConfig_475_);
v_val_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = lean_array_to_list(v_testDriverArgs_480_);
v___x_578_ = l_List_appendTR___redArg(v___x_577_, v_args_474_);
v___x_579_ = l_Lake_Script_run(v___x_578_, v_val_576_, v_a_476_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
lean_dec(v___x_575_);
v___x_580_ = l_Lake_Package_findTargetDecl_x3f(v___x_574_, v_fst_487_);
lean_dec(v___x_574_);
if (lean_obj_tag(v___x_580_) == 0)
{
goto v___jp_511_;
}
else
{
lean_object* v_val_581_; lean_object* v_name_582_; lean_object* v_kind_583_; lean_object* v_config_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v___x_580_, 1);
v_name_582_ = lean_ctor_get(v_val_581_, 1);
lean_inc(v_name_582_);
v_kind_583_ = lean_ctor_get(v_val_581_, 2);
lean_inc(v_kind_583_);
v_config_584_ = lean_ctor_get(v_val_581_, 3);
lean_inc(v_config_584_);
lean_dec(v_val_581_);
v___x_585_ = l_Lake_LeanExe_keyword;
v___x_586_ = lean_name_eq(v_kind_583_, v___x_585_);
lean_dec(v_kind_583_);
if (v___x_586_ == 0)
{
lean_dec(v_config_584_);
lean_dec(v_name_582_);
goto v___jp_511_;
}
else
{
lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___x_589_; 
lean_dec(v_snd_488_);
lean_del_object(v___x_485_);
lean_inc(v_name_582_);
v___x_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_587_, 0, v_fst_487_);
lean_ctor_set(v___x_587_, 1, v_name_582_);
lean_ctor_set(v___x_587_, 2, v_config_584_);
v___f_588_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_588_, 0, v_keyName_490_);
lean_closure_set(v___f_588_, 1, v_name_582_);
lean_closure_set(v___f_588_, 2, v___x_585_);
lean_closure_set(v___f_588_, 3, v___x_587_);
lean_inc(v_a_476_);
v___x_589_ = l_Lake_Workspace_runBuild___redArg(v_a_476_, v___f_588_, v_buildConfig_475_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_array_mk(v_args_474_);
v___x_592_ = l_Array_append___redArg(v_testDriverArgs_480_, v___x_591_);
lean_dec_ref(v___x_591_);
v___x_593_ = l_Lake_env(v_a_590_, v___x_592_, v_a_476_);
return v___x_593_;
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v_testDriverArgs_480_);
lean_dec(v_args_474_);
v_a_594_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_589_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_589_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
}
v___jp_492_:
{
uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_493_ = 0;
v___x_494_ = l_Lean_Name_toString(v_baseName_489_, v___x_493_);
v___x_495_ = ((lean_object*)(l_Lake_Package_test___closed__1));
v___x_496_ = lean_string_append(v___x_494_, v___x_495_);
v___x_497_ = lean_string_append(v___x_496_, v_snd_488_);
lean_dec(v_snd_488_);
v___x_498_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_499_ = lean_string_append(v___x_497_, v___x_498_);
v___x_500_ = lean_mk_io_user_error(v___x_499_);
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 1);
lean_ctor_set(v___x_485_, 0, v___x_500_);
v___x_502_ = v___x_485_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
v___jp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_506_ = l_Lean_Name_toString(v_baseName_489_, v___y_505_);
v___x_507_ = ((lean_object*)(l_Lake_Package_test___closed__2));
v___x_508_ = lean_string_append(v___x_506_, v___x_507_);
v___x_509_ = lean_mk_io_user_error(v___x_508_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
v___jp_511_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_inc(v_snd_488_);
v___x_512_ = l_String_toName(v_snd_488_);
v___x_513_ = l_Lake_Package_findTargetDecl_x3f(v___x_512_, v_fst_487_);
lean_dec(v___x_512_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_inc(v_baseName_489_);
lean_dec(v_keyName_490_);
lean_dec(v_fst_487_);
lean_dec_ref(v_testDriverArgs_480_);
lean_dec_ref(v_buildConfig_475_);
lean_dec(v_args_474_);
goto v___jp_492_;
}
else
{
lean_object* v_val_514_; lean_object* v_name_515_; lean_object* v_kind_516_; lean_object* v_config_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_val_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_514_);
lean_dec_ref_known(v___x_513_, 1);
v_name_515_ = lean_ctor_get(v_val_514_, 1);
lean_inc(v_name_515_);
v_kind_516_ = lean_ctor_get(v_val_514_, 2);
lean_inc(v_kind_516_);
v_config_517_ = lean_ctor_get(v_val_514_, 3);
lean_inc(v_config_517_);
lean_dec(v_val_514_);
v___x_518_ = ((lean_object*)(l_Lake_Package_test___closed__4));
v___x_519_ = lean_name_eq(v_kind_516_, v___x_518_);
lean_dec(v_kind_516_);
if (v___x_519_ == 0)
{
lean_inc(v_baseName_489_);
lean_dec(v_config_517_);
lean_dec(v_name_515_);
lean_dec(v_keyName_490_);
lean_dec(v_fst_487_);
lean_dec_ref(v_testDriverArgs_480_);
lean_dec_ref(v_buildConfig_475_);
lean_dec(v_args_474_);
goto v___jp_492_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
lean_dec(v_snd_488_);
lean_del_object(v___x_485_);
v___x_520_ = lean_array_get_size(v_testDriverArgs_480_);
lean_dec_ref(v_testDriverArgs_480_);
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = lean_nat_dec_eq(v___x_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_inc(v_baseName_489_);
lean_dec(v_config_517_);
lean_dec(v_name_515_);
lean_dec(v_keyName_490_);
lean_dec(v_fst_487_);
lean_dec_ref(v_buildConfig_475_);
lean_dec(v_args_474_);
v___y_505_ = v___x_522_;
goto v___jp_504_;
}
else
{
uint8_t v___x_523_; 
v___x_523_ = l_List_isEmpty___redArg(v_args_474_);
lean_dec(v_args_474_);
if (v___x_523_ == 0)
{
lean_inc(v_baseName_489_);
lean_dec(v_config_517_);
lean_dec(v_name_515_);
lean_dec(v_keyName_490_);
lean_dec(v_fst_487_);
lean_dec_ref(v_buildConfig_475_);
v___y_505_ = v___x_523_;
goto v___jp_504_;
}
else
{
lean_object* v_toLogConfig_524_; uint8_t v_oldMode_525_; uint8_t v_trustHash_526_; uint8_t v_noBuild_527_; uint8_t v_failFast_528_; uint8_t v_verbosity_529_; uint8_t v_showSuccess_530_; lean_object* v_outputsFile_x3f_531_; lean_object* v_outputsIdx_532_; lean_object* v_leanOptOverrides_533_; lean_object* v_macosxDeploymentTarget_x3f_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_573_; 
v_toLogConfig_524_ = lean_ctor_get(v_buildConfig_475_, 0);
v_oldMode_525_ = lean_ctor_get_uint8(v_buildConfig_475_, sizeof(void*)*5);
v_trustHash_526_ = lean_ctor_get_uint8(v_buildConfig_475_, sizeof(void*)*5 + 1);
v_noBuild_527_ = lean_ctor_get_uint8(v_buildConfig_475_, sizeof(void*)*5 + 2);
v_failFast_528_ = lean_ctor_get_uint8(v_buildConfig_475_, sizeof(void*)*5 + 3);
v_verbosity_529_ = lean_ctor_get_uint8(v_buildConfig_475_, sizeof(void*)*5 + 4);
v_showSuccess_530_ = lean_ctor_get_uint8(v_buildConfig_475_, sizeof(void*)*5 + 5);
v_outputsFile_x3f_531_ = lean_ctor_get(v_buildConfig_475_, 1);
v_outputsIdx_532_ = lean_ctor_get(v_buildConfig_475_, 2);
v_leanOptOverrides_533_ = lean_ctor_get(v_buildConfig_475_, 3);
v_macosxDeploymentTarget_x3f_534_ = lean_ctor_get(v_buildConfig_475_, 4);
v_isSharedCheck_573_ = !lean_is_exclusive(v_buildConfig_475_);
if (v_isSharedCheck_573_ == 0)
{
v___x_536_ = v_buildConfig_475_;
v_isShared_537_ = v_isSharedCheck_573_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_macosxDeploymentTarget_x3f_534_);
lean_inc(v_leanOptOverrides_533_);
lean_inc(v_outputsIdx_532_);
lean_inc(v_outputsFile_x3f_531_);
lean_inc(v_toLogConfig_524_);
lean_dec(v_buildConfig_475_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_573_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v_failLv_538_; uint8_t v_outLv_539_; uint8_t v_ansiMode_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_571_; 
v_failLv_538_ = lean_ctor_get_uint8(v_toLogConfig_524_, sizeof(void*)*1);
v_outLv_539_ = lean_ctor_get_uint8(v_toLogConfig_524_, sizeof(void*)*1 + 1);
v_ansiMode_540_ = lean_ctor_get_uint8(v_toLogConfig_524_, sizeof(void*)*1 + 2);
v_isSharedCheck_571_ = !lean_is_exclusive(v_toLogConfig_524_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v_toLogConfig_524_, 0);
lean_dec(v_unused_572_);
v___x_542_ = v_toLogConfig_524_;
v_isShared_543_ = v_isSharedCheck_571_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_toLogConfig_524_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_571_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___f_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
lean_inc(v_name_515_);
v___x_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_544_, 0, v_fst_487_);
lean_ctor_set(v___x_544_, 1, v_name_515_);
lean_ctor_set(v___x_544_, 2, v_config_517_);
v___f_545_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0___boxed), 11, 4);
lean_closure_set(v___f_545_, 0, v_keyName_490_);
lean_closure_set(v___f_545_, 1, v_name_515_);
lean_closure_set(v___f_545_, 2, v___x_518_);
lean_closure_set(v___f_545_, 3, v___x_544_);
v___x_546_ = lean_box(0);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_546_);
v___x_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*1, v_failLv_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*1 + 1, v_outLv_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*1 + 2, v_ansiMode_540_);
v___x_548_ = v_reuseFailAlloc_570_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_550_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_548_);
v___x_550_ = v___x_536_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 6);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_outputsFile_x3f_531_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_outputsIdx_532_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_leanOptOverrides_533_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_macosxDeploymentTarget_x3f_534_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*5, v_oldMode_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*5 + 1, v_trustHash_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*5 + 2, v_noBuild_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*5 + 3, v_failFast_528_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*5 + 4, v_verbosity_529_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*5 + 5, v_showSuccess_530_);
v___x_550_ = v_reuseFailAlloc_569_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
lean_inc(v_a_476_);
v___x_551_ = l_Lake_Workspace_runBuild___redArg(v_a_476_, v___f_545_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_551_, 0);
lean_dec(v_unused_560_);
v___x_553_ = v___x_551_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_dec(v___x_551_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_Lake_Package_test___boxed__const__1;
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_551_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_551_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
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
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_testDriverArgs_480_);
lean_dec_ref(v_buildConfig_475_);
lean_dec(v_args_474_);
v_a_603_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_482_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_482_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_test_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_473_ = stack[0].m_obj;
lean_object* v_args_474_ = stack[1].m_obj;
lean_object* v_buildConfig_475_ = stack[2].m_obj;
lean_object* v_a_476_ = stack[3].m_obj;
lean_object* v_res_611_;
v_res_611_ = l_Lake_Package_test(v_pkg_473_, v_args_474_, v_buildConfig_475_, v_a_476_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed(lean_object* v_pkg_612_, lean_object* v_args_613_, lean_object* v_buildConfig_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lake_Package_test(v_pkg_612_, v_args_613_, v_buildConfig_614_, v_a_615_);
lean_dec(v_a_615_);
return v_res_617_;
}
}
lean_object* l_Lake_Package_lint(lean_object* v_pkg_620_, lean_object* v_args_621_, lean_object* v_buildConfig_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_config_625_; lean_object* v_lintDriver_626_; lean_object* v_lintDriverArgs_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_config_625_ = lean_ctor_get(v_pkg_620_, 6);
v_lintDriver_626_ = lean_ctor_get(v_pkg_620_, 23);
lean_inc_ref(v_lintDriver_626_);
v_lintDriverArgs_627_ = lean_ctor_get(v_config_625_, 15);
lean_inc_ref(v_lintDriverArgs_627_);
v___x_628_ = ((lean_object*)(l_Lake_Package_lint___closed__0));
v___x_629_ = l_Lake_Package_resolveDriver(v_pkg_620_, v___x_628_, v_lintDriver_626_, v_a_623_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_679_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_679_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_679_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_679_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_fst_634_; lean_object* v_snd_635_; lean_object* v_baseName_636_; lean_object* v_keyName_637_; lean_object* v_scripts_638_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_fst_634_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_fst_634_);
v_snd_635_ = lean_ctor_get(v_a_630_, 1);
lean_inc_n(v_snd_635_, 2);
lean_dec(v_a_630_);
v_baseName_636_ = lean_ctor_get(v_fst_634_, 1);
v_keyName_637_ = lean_ctor_get(v_fst_634_, 2);
lean_inc(v_keyName_637_);
v_scripts_638_ = lean_ctor_get(v_fst_634_, 18);
v___x_651_ = l_String_toName(v_snd_635_);
v___x_652_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_638_, v___x_651_);
if (lean_obj_tag(v___x_652_) == 1)
{
lean_object* v_val_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v___x_651_);
lean_dec(v_keyName_637_);
lean_dec(v_snd_635_);
lean_dec(v_fst_634_);
lean_del_object(v___x_632_);
lean_dec_ref(v_buildConfig_622_);
v_val_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = lean_array_to_list(v_lintDriverArgs_627_);
v___x_655_ = l_List_appendTR___redArg(v___x_654_, v_args_621_);
v___x_656_ = l_Lake_Script_run(v___x_655_, v_val_653_, v_a_623_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
lean_dec(v___x_652_);
v___x_657_ = l_Lake_Package_findTargetDecl_x3f(v___x_651_, v_fst_634_);
lean_dec(v___x_651_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_inc(v_baseName_636_);
lean_dec(v_keyName_637_);
lean_dec(v_fst_634_);
lean_dec_ref(v_lintDriverArgs_627_);
lean_dec_ref(v_buildConfig_622_);
lean_dec(v_args_621_);
goto v___jp_639_;
}
else
{
lean_object* v_val_658_; lean_object* v_name_659_; lean_object* v_kind_660_; lean_object* v_config_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_val_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v___x_657_, 1);
v_name_659_ = lean_ctor_get(v_val_658_, 1);
lean_inc(v_name_659_);
v_kind_660_ = lean_ctor_get(v_val_658_, 2);
lean_inc(v_kind_660_);
v_config_661_ = lean_ctor_get(v_val_658_, 3);
lean_inc(v_config_661_);
lean_dec(v_val_658_);
v___x_662_ = l_Lake_LeanExe_keyword;
v___x_663_ = lean_name_eq(v_kind_660_, v___x_662_);
lean_dec(v_kind_660_);
if (v___x_663_ == 0)
{
lean_inc(v_baseName_636_);
lean_dec(v_config_661_);
lean_dec(v_name_659_);
lean_dec(v_keyName_637_);
lean_dec(v_fst_634_);
lean_dec_ref(v_lintDriverArgs_627_);
lean_dec_ref(v_buildConfig_622_);
lean_dec(v_args_621_);
goto v___jp_639_;
}
else
{
lean_object* v___x_664_; lean_object* v___f_665_; lean_object* v___x_666_; 
lean_dec(v_snd_635_);
lean_del_object(v___x_632_);
lean_inc(v_name_659_);
v___x_664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_664_, 0, v_fst_634_);
lean_ctor_set(v___x_664_, 1, v_name_659_);
lean_ctor_set(v___x_664_, 2, v_config_661_);
v___f_665_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_665_, 0, v_keyName_637_);
lean_closure_set(v___f_665_, 1, v_name_659_);
lean_closure_set(v___f_665_, 2, v___x_662_);
lean_closure_set(v___f_665_, 3, v___x_664_);
lean_inc(v_a_623_);
v___x_666_ = l_Lake_Workspace_runBuild___redArg(v_a_623_, v___f_665_, v_buildConfig_622_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_array_mk(v_args_621_);
v___x_669_ = l_Array_append___redArg(v_lintDriverArgs_627_, v___x_668_);
lean_dec_ref(v___x_668_);
v___x_670_ = l_Lake_env(v_a_667_, v___x_669_, v_a_623_);
return v___x_670_;
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_lintDriverArgs_627_);
lean_dec(v_args_621_);
v_a_671_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_666_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_666_);
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
}
v___jp_639_:
{
uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_640_ = 0;
v___x_641_ = l_Lean_Name_toString(v_baseName_636_, v___x_640_);
v___x_642_ = ((lean_object*)(l_Lake_Package_lint___closed__1));
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
v___x_644_ = lean_string_append(v___x_643_, v_snd_635_);
lean_dec(v_snd_635_);
v___x_645_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
v___x_647_ = lean_mk_io_user_error(v___x_646_);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
lean_ctor_set(v___x_632_, 0, v___x_647_);
v___x_649_ = v___x_632_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec_ref(v_lintDriverArgs_627_);
lean_dec_ref(v_buildConfig_622_);
lean_dec(v_args_621_);
v_a_680_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_629_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_629_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Package_lint_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_620_ = stack[0].m_obj;
lean_object* v_args_621_ = stack[1].m_obj;
lean_object* v_buildConfig_622_ = stack[2].m_obj;
lean_object* v_a_623_ = stack[3].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Lake_Package_lint(v_pkg_620_, v_args_621_, v_buildConfig_622_, v_a_623_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_Lake_Package_lint___boxed(lean_object* v_pkg_689_, lean_object* v_args_690_, lean_object* v_buildConfig_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lake_Package_lint(v_pkg_689_, v_args_690_, v_buildConfig_691_, v_a_692_);
lean_dec(v_a_692_);
return v_res_694_;
}
}
lean_object* l_Lake_Workspace_evalLeanFile(lean_object* v_ws_695_, lean_object* v_leanFile_696_, lean_object* v_moreArgs_697_, lean_object* v_buildConfig_698_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_alloc_closure((void*)(l_Lake_prepareLeanCommand___boxed), 9, 2);
lean_closure_set(v___x_700_, 0, v_leanFile_696_);
lean_closure_set(v___x_700_, 1, v_moreArgs_697_);
v___x_701_ = l_Lake_Workspace_runBuild___redArg(v_ws_695_, v___x_700_, v_buildConfig_698_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc_n(v_a_702_, 2);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_io_process_spawn(v_a_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v_toStdioConfig_705_; lean_object* v___x_706_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v_toStdioConfig_705_ = lean_ctor_get(v_a_702_, 0);
lean_inc_ref(v_toStdioConfig_705_);
lean_dec(v_a_702_);
v___x_706_ = lean_io_process_child_wait(v_toStdioConfig_705_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_toStdioConfig_705_);
return v___x_706_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_a_702_);
v_a_707_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_703_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_703_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_701_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_701_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Workspace_evalLeanFile_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_695_ = stack[0].m_obj;
lean_object* v_leanFile_696_ = stack[1].m_obj;
lean_object* v_moreArgs_697_ = stack[2].m_obj;
lean_object* v_buildConfig_698_ = stack[3].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Lake_Workspace_evalLeanFile(v_ws_695_, v_leanFile_696_, v_moreArgs_697_, v_buildConfig_698_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile___boxed(lean_object* v_ws_724_, lean_object* v_leanFile_725_, lean_object* v_moreArgs_726_, lean_object* v_buildConfig_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lake_Workspace_evalLeanFile(v_ws_724_, v_leanFile_725_, v_moreArgs_726_, v_buildConfig_727_);
return v_res_729_;
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
