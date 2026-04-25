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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
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
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0_value;
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
lean_dec_ref(v___x_13_);
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
lean_dec_ref(v___x_61_);
v___f_63_ = lean_alloc_closure((void*)(l_Lake_exe___lam__0___boxed), 8, 1);
lean_closure_set(v___f_63_, 0, v_val_62_);
lean_inc(v_a_59_);
v___x_64_ = l_Lake_Workspace_runBuild___redArg(v_a_59_, v___f_63_, v_buildConfig_58_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v___x_66_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_a_65_);
lean_dec_ref(v___x_64_);
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
v_buildArchive_173_ = lean_ctor_get(v_pkg_156_, 20);
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
lean_dec_ref(v___x_177_);
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
lean_dec_ref(v_releaseRepo_179_);
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
v___x_170_ = l_Lake_proc(v___x_169_, v___x_168_, v___y_162_);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(lean_object* v_s_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___closed__0));
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0___boxed(lean_object* v_s_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(v_s_206_);
lean_dec_ref(v_s_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(lean_object* v___x_211_, lean_object* v_as_212_, size_t v_sz_213_, size_t v_i_214_, lean_object* v_b_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_lt(v_i_214_, v_sz_213_);
if (v___x_216_ == 0)
{
lean_inc_ref(v_b_215_);
return v_b_215_;
}
else
{
lean_object* v_a_217_; lean_object* v_baseName_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_a_217_ = lean_array_uget_borrowed(v_as_212_, v_i_214_);
v_baseName_218_ = lean_ctor_get(v_a_217_, 1);
v___x_219_ = lean_box(0);
v___x_220_ = lean_name_eq(v_baseName_218_, v___x_211_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; 
v___x_221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0));
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_i_214_, v___x_222_);
v_i_214_ = v___x_223_;
v_b_215_ = v___x_221_;
goto _start;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
lean_inc(v_a_217_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_a_217_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_219_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___boxed(lean_object* v___x_228_, lean_object* v_as_229_, lean_object* v_sz_230_, lean_object* v_i_231_, lean_object* v_b_232_){
_start:
{
size_t v_sz_boxed_233_; size_t v_i_boxed_234_; lean_object* v_res_235_; 
v_sz_boxed_233_ = lean_unbox_usize(v_sz_230_);
lean_dec(v_sz_230_);
v_i_boxed_234_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_228_, v_as_229_, v_sz_boxed_233_, v_i_boxed_234_, v_b_232_);
lean_dec_ref(v_b_232_);
lean_dec_ref(v_as_229_);
lean_dec(v___x_228_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(lean_object* v_driver_236_, lean_object* v___x_237_, lean_object* v___x_238_, lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
lean_object* v_it_242_; lean_object* v_startInclusive_243_; lean_object* v_endExclusive_244_; 
if (lean_obj_tag(v_a_239_) == 0)
{
lean_object* v_currPos_249_; lean_object* v_searcher_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_276_; 
v_currPos_249_ = lean_ctor_get(v_a_239_, 0);
v_searcher_250_ = lean_ctor_get(v_a_239_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_a_239_);
if (v_isSharedCheck_276_ == 0)
{
v___x_252_ = v_a_239_;
v_isShared_253_ = v_isSharedCheck_276_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_searcher_250_);
lean_inc(v_currPos_249_);
lean_dec(v_a_239_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_276_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_startInclusive_254_; lean_object* v_endExclusive_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_startInclusive_254_ = lean_ctor_get(v___x_237_, 1);
v_endExclusive_255_ = lean_ctor_get(v___x_237_, 2);
v___x_256_ = lean_nat_sub(v_endExclusive_255_, v_startInclusive_254_);
v___x_257_ = lean_nat_dec_eq(v_searcher_250_, v___x_256_);
lean_dec(v___x_256_);
if (v___x_257_ == 0)
{
uint32_t v___x_258_; uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_258_ = 47;
v___x_259_ = lean_string_utf8_get_fast(v_driver_236_, v_searcher_250_);
v___x_260_ = lean_uint32_dec_eq(v___x_259_, v___x_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_string_utf8_next_fast(v_driver_236_, v_searcher_250_);
lean_dec(v_searcher_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_261_);
v___x_263_ = v___x_252_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_currPos_249_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
v_a_239_ = v___x_263_;
goto _start;
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_slice_269_; lean_object* v_nextIt_271_; 
v___x_266_ = lean_string_utf8_next_fast(v_driver_236_, v_searcher_250_);
v___x_267_ = lean_nat_sub(v___x_266_, v_searcher_250_);
v___x_268_ = lean_nat_add(v_searcher_250_, v___x_267_);
lean_dec(v___x_267_);
v_slice_269_ = l_String_Slice_subslice_x21(v___x_237_, v_currPos_249_, v_searcher_250_);
lean_inc(v___x_268_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_268_);
lean_ctor_set(v___x_252_, 0, v___x_268_);
v_nextIt_271_ = v___x_252_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_268_);
v_nextIt_271_ = v_reuseFailAlloc_274_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v_startInclusive_272_; lean_object* v_endExclusive_273_; 
v_startInclusive_272_ = lean_ctor_get(v_slice_269_, 0);
lean_inc(v_startInclusive_272_);
v_endExclusive_273_ = lean_ctor_get(v_slice_269_, 1);
lean_inc(v_endExclusive_273_);
lean_dec_ref(v_slice_269_);
v_it_242_ = v_nextIt_271_;
v_startInclusive_243_ = v_startInclusive_272_;
v_endExclusive_244_ = v_endExclusive_273_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v___x_275_; 
lean_del_object(v___x_252_);
lean_dec(v_searcher_250_);
v___x_275_ = lean_box(1);
lean_inc(v___x_238_);
v_it_242_ = v___x_275_;
v_startInclusive_243_ = v_currPos_249_;
v_endExclusive_244_ = v___x_238_;
goto v___jp_241_;
}
}
}
else
{
lean_dec(v___x_238_);
lean_dec_ref(v_driver_236_);
return v_b_240_;
}
v___jp_241_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_inc_ref(v_driver_236_);
v___x_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_245_, 0, v_driver_236_);
lean_ctor_set(v___x_245_, 1, v_startInclusive_243_);
lean_ctor_set(v___x_245_, 2, v_endExclusive_244_);
v___x_246_ = l_String_Slice_toString(v___x_245_);
lean_dec_ref(v___x_245_);
v___x_247_ = lean_array_push(v_b_240_, v___x_246_);
v_a_239_ = v_it_242_;
v_b_240_ = v___x_247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object* v_driver_277_, lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_277_, v___x_278_, v___x_279_, v_a_280_, v_b_281_);
lean_dec_ref(v___x_278_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object* v_pkg_291_, lean_object* v_kind_292_, lean_object* v_driver_293_, lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = lean_string_utf8_byte_size(v_driver_293_);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_nat_dec_eq(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_inc_ref_n(v_driver_293_, 2);
v___x_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_312_, 0, v_driver_293_);
lean_ctor_set(v___x_312_, 1, v___x_297_);
lean_ctor_set(v___x_312_, 2, v___x_296_);
v___x_313_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(v___x_312_);
v___x_314_ = ((lean_object*)(l_Lake_Package_pack___closed__1));
v___x_315_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_293_, v___x_312_, v___x_296_, v___x_313_, v___x_314_);
lean_dec_ref(v___x_312_);
v___x_316_ = lean_array_to_list(v___x_315_);
if (lean_obj_tag(v___x_316_) == 1)
{
lean_object* v_head_317_; lean_object* v_tail_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_365_; 
v_head_317_ = lean_ctor_get(v___x_316_, 0);
v_tail_318_ = lean_ctor_get(v___x_316_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_365_ == 0)
{
v___x_320_ = v___x_316_;
v_isShared_321_ = v_isSharedCheck_365_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_tail_318_);
lean_inc(v_head_317_);
lean_dec(v___x_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_365_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
if (lean_obj_tag(v_tail_318_) == 0)
{
lean_object* v___x_336_; 
lean_dec_ref(v_driver_293_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 0);
lean_ctor_set(v___x_320_, 1, v_head_317_);
lean_ctor_set(v___x_320_, 0, v_pkg_291_);
v___x_336_ = v___x_320_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_pkg_291_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_head_317_);
v___x_336_ = v_reuseFailAlloc_338_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
else
{
lean_object* v_tail_339_; 
lean_del_object(v___x_320_);
v_tail_339_ = lean_ctor_get(v_tail_318_, 1);
if (lean_obj_tag(v_tail_339_) == 0)
{
lean_object* v_head_340_; lean_object* v_packages_341_; lean_object* v___x_342_; lean_object* v___x_343_; size_t v_sz_344_; size_t v___x_345_; lean_object* v___x_346_; lean_object* v_fst_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v_driver_293_);
v_head_340_ = lean_ctor_get(v_tail_318_, 0);
lean_inc(v_head_340_);
lean_dec_ref(v_tail_318_);
v_packages_341_ = lean_ctor_get(v_a_294_, 4);
lean_inc(v_head_317_);
v___x_342_ = l_String_toName(v_head_317_);
v___x_343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0));
v_sz_344_ = lean_array_size(v_packages_341_);
v___x_345_ = ((size_t)0ULL);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_342_, v_packages_341_, v_sz_344_, v___x_345_, v___x_343_);
lean_dec(v___x_342_);
v_fst_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v___x_346_, 1);
lean_dec(v_unused_364_);
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_fst_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
if (lean_obj_tag(v_fst_347_) == 0)
{
lean_del_object(v___x_349_);
lean_dec(v_head_340_);
goto v___jp_322_;
}
else
{
lean_object* v_val_351_; 
v_val_351_ = lean_ctor_get(v_fst_347_, 0);
lean_inc(v_val_351_);
lean_dec_ref(v_fst_347_);
if (lean_obj_tag(v_val_351_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_head_317_);
lean_dec_ref(v_pkg_291_);
v_val_352_ = lean_ctor_get(v_val_351_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v_val_351_);
if (v_isSharedCheck_362_ == 0)
{
v___x_354_ = v_val_351_;
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_val_352_);
lean_dec(v_val_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_head_340_);
lean_ctor_set(v___x_349_, 0, v_val_352_);
v___x_357_ = v___x_349_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_val_352_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_head_340_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 0);
lean_ctor_set(v___x_354_, 0, v___x_357_);
v___x_359_ = v___x_354_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_dec(v_val_351_);
lean_del_object(v___x_349_);
lean_dec(v_head_340_);
goto v___jp_322_;
}
}
}
}
else
{
lean_dec_ref(v_tail_318_);
lean_dec(v_head_317_);
goto v___jp_299_;
}
}
v___jp_322_:
{
lean_object* v_baseName_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_baseName_323_ = lean_ctor_get(v_pkg_291_, 1);
lean_inc(v_baseName_323_);
lean_dec_ref(v_pkg_291_);
v___x_324_ = l_Lean_Name_toString(v_baseName_323_, v___x_298_);
v___x_325_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__3));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
v___x_327_ = lean_string_append(v___x_326_, v_kind_292_);
v___x_328_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__4));
v___x_329_ = lean_string_append(v___x_327_, v___x_328_);
v___x_330_ = lean_string_append(v___x_329_, v_head_317_);
lean_dec(v_head_317_);
v___x_331_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_332_ = lean_string_append(v___x_330_, v___x_331_);
v___x_333_ = lean_mk_io_user_error(v___x_332_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
else
{
lean_dec(v___x_316_);
goto v___jp_299_;
}
}
else
{
lean_object* v_baseName_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_dec_ref(v_driver_293_);
v_baseName_366_ = lean_ctor_get(v_pkg_291_, 1);
lean_inc(v_baseName_366_);
lean_dec_ref(v_pkg_291_);
v___x_367_ = 0;
v___x_368_ = l_Lean_Name_toString(v_baseName_366_, v___x_367_);
v___x_369_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__6));
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
v___x_371_ = lean_string_append(v___x_370_, v_kind_292_);
v___x_372_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__7));
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
v___x_374_ = lean_mk_io_user_error(v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
v___jp_299_:
{
lean_object* v_baseName_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_baseName_300_ = lean_ctor_get(v_pkg_291_, 1);
lean_inc(v_baseName_300_);
lean_dec_ref(v_pkg_291_);
v___x_301_ = l_Lean_Name_toString(v_baseName_300_, v___x_298_);
v___x_302_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__0));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
v___x_304_ = lean_string_append(v___x_303_, v_kind_292_);
v___x_305_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__1));
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
v___x_307_ = lean_string_append(v___x_306_, v_driver_293_);
lean_dec_ref(v_driver_293_);
v___x_308_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__2));
v___x_309_ = lean_string_append(v___x_307_, v___x_308_);
v___x_310_ = lean_mk_io_user_error(v___x_309_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object* v_pkg_376_, lean_object* v_kind_377_, lean_object* v_driver_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lake_Package_resolveDriver(v_pkg_376_, v_kind_377_, v_driver_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_kind_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(lean_object* v_driver_382_, lean_object* v___x_383_, lean_object* v___x_384_, lean_object* v_inst_385_, lean_object* v_R_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_382_, v___x_383_, v___x_384_, v_a_387_, v_b_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___boxed(lean_object* v_driver_390_, lean_object* v___x_391_, lean_object* v___x_392_, lean_object* v_inst_393_, lean_object* v_R_394_, lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(v_driver_390_, v___x_391_, v___x_392_, v_inst_393_, v_R_394_, v_a_395_, v_b_396_);
lean_dec_ref(v___x_391_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object* v_keyName_398_, lean_object* v_name_399_, lean_object* v___x_400_, lean_object* v___x_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = l_Lake_LeanLib_defaultFacet;
v___x_410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_410_, 0, v_keyName_398_);
lean_ctor_set(v___x_410_, 1, v_name_399_);
v___x_411_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_400_);
lean_ctor_set(v___x_411_, 2, v___x_401_);
lean_ctor_set(v___x_411_, 3, v___x_409_);
v___x_412_ = lean_apply_7(v___y_402_, v___x_411_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0___boxed(lean_object* v_keyName_413_, lean_object* v_name_414_, lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lake_Package_test___lam__0(v_keyName_413_, v_name_414_, v___x_415_, v___x_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object* v_keyName_425_, lean_object* v_name_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = l_Lake_LeanExe_exeFacet;
v___x_437_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_437_, 0, v_keyName_425_);
lean_ctor_set(v___x_437_, 1, v_name_426_);
v___x_438_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_427_);
lean_ctor_set(v___x_438_, 2, v___x_428_);
lean_ctor_set(v___x_438_, 3, v___x_436_);
v___x_439_ = lean_apply_7(v___y_429_, v___x_438_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, lean_box(0));
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1___boxed(lean_object* v_keyName_440_, lean_object* v_name_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_Package_test___lam__1(v_keyName_440_, v_name_441_, v___x_442_, v___x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
return v_res_451_;
}
}
static lean_object* _init_l_Lake_Package_test___boxed__const__1(void){
_start:
{
uint32_t v___x_458_; lean_object* v___x_459_; 
v___x_458_ = 0;
v___x_459_ = lean_box_uint32(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* v_pkg_460_, lean_object* v_args_461_, lean_object* v_buildConfig_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_config_465_; lean_object* v_testDriver_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_config_465_ = lean_ctor_get(v_pkg_460_, 6);
lean_inc_ref(v_config_465_);
v_testDriver_466_ = lean_ctor_get(v_pkg_460_, 21);
lean_inc_ref(v_testDriver_466_);
v___x_467_ = ((lean_object*)(l_Lake_Package_test___closed__0));
v___x_468_ = l_Lake_Package_resolveDriver(v_pkg_460_, v___x_467_, v_testDriver_466_, v_a_463_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_585_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_585_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_585_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_585_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v_testDriverArgs_475_; lean_object* v_baseName_476_; lean_object* v_keyName_477_; lean_object* v_scripts_478_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_fst_473_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_fst_473_);
v_snd_474_ = lean_ctor_get(v_a_469_, 1);
lean_inc_n(v_snd_474_, 2);
lean_dec(v_a_469_);
v_testDriverArgs_475_ = lean_ctor_get(v_config_465_, 13);
lean_inc_ref(v_testDriverArgs_475_);
lean_dec_ref(v_config_465_);
v_baseName_476_ = lean_ctor_get(v_fst_473_, 1);
v_keyName_477_ = lean_ctor_get(v_fst_473_, 2);
lean_inc(v_keyName_477_);
v_scripts_478_ = lean_ctor_get(v_fst_473_, 17);
v___x_557_ = l_String_toName(v_snd_474_);
v___x_558_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_478_, v___x_557_);
if (lean_obj_tag(v___x_558_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_557_);
lean_dec(v_keyName_477_);
lean_dec(v_snd_474_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec_ref(v_buildConfig_462_);
v_val_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_559_);
lean_dec_ref(v___x_558_);
v___x_560_ = lean_array_to_list(v_testDriverArgs_475_);
v___x_561_ = l_List_appendTR___redArg(v___x_560_, v_args_461_);
v___x_562_ = l_Lake_Script_run(v___x_561_, v_val_559_, v_a_463_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; 
lean_dec(v___x_558_);
v___x_563_ = l_Lake_Package_findTargetDecl_x3f(v___x_557_, v_fst_473_);
lean_dec(v___x_557_);
if (lean_obj_tag(v___x_563_) == 0)
{
goto v___jp_498_;
}
else
{
lean_object* v_val_564_; lean_object* v_name_565_; lean_object* v_kind_566_; lean_object* v_config_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_val_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_564_);
lean_dec_ref(v___x_563_);
v_name_565_ = lean_ctor_get(v_val_564_, 1);
lean_inc(v_name_565_);
v_kind_566_ = lean_ctor_get(v_val_564_, 2);
lean_inc(v_kind_566_);
v_config_567_ = lean_ctor_get(v_val_564_, 3);
lean_inc(v_config_567_);
lean_dec(v_val_564_);
v___x_568_ = l_Lake_LeanExe_keyword;
v___x_569_ = lean_name_eq(v_kind_566_, v___x_568_);
lean_dec(v_kind_566_);
if (v___x_569_ == 0)
{
lean_dec(v_config_567_);
lean_dec(v_name_565_);
goto v___jp_498_;
}
else
{
lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
lean_dec(v_snd_474_);
lean_del_object(v___x_471_);
lean_inc(v_name_565_);
v___x_570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_570_, 0, v_fst_473_);
lean_ctor_set(v___x_570_, 1, v_name_565_);
lean_ctor_set(v___x_570_, 2, v_config_567_);
v___f_571_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_571_, 0, v_keyName_477_);
lean_closure_set(v___f_571_, 1, v_name_565_);
lean_closure_set(v___f_571_, 2, v___x_568_);
lean_closure_set(v___f_571_, 3, v___x_570_);
lean_inc(v_a_463_);
v___x_572_ = l_Lake_Workspace_runBuild___redArg(v_a_463_, v___f_571_, v_buildConfig_462_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref(v___x_572_);
v___x_574_ = lean_array_mk(v_args_461_);
v___x_575_ = l_Array_append___redArg(v_testDriverArgs_475_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lake_env(v_a_573_, v___x_575_, v_a_463_);
return v___x_576_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v_testDriverArgs_475_);
lean_dec(v_args_461_);
v_a_577_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_572_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_572_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
v___jp_479_:
{
uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_480_ = 0;
v___x_481_ = l_Lean_Name_toString(v_baseName_476_, v___x_480_);
v___x_482_ = ((lean_object*)(l_Lake_Package_test___closed__1));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_484_ = lean_mk_io_user_error(v___x_483_);
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 1);
lean_ctor_set(v___x_471_, 0, v___x_484_);
v___x_486_ = v___x_471_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
v___jp_488_:
{
uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_489_ = 0;
v___x_490_ = l_Lean_Name_toString(v_baseName_476_, v___x_489_);
v___x_491_ = ((lean_object*)(l_Lake_Package_test___closed__2));
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
v___x_493_ = lean_string_append(v___x_492_, v_snd_474_);
lean_dec(v_snd_474_);
v___x_494_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_495_ = lean_string_append(v___x_493_, v___x_494_);
v___x_496_ = lean_mk_io_user_error(v___x_495_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
v___jp_498_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_inc(v_snd_474_);
v___x_499_ = l_String_toName(v_snd_474_);
v___x_500_ = l_Lake_Package_findTargetDecl_x3f(v___x_499_, v_fst_473_);
lean_dec(v___x_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_inc(v_baseName_476_);
lean_dec(v_keyName_477_);
lean_dec_ref(v_testDriverArgs_475_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec_ref(v_buildConfig_462_);
lean_dec(v_args_461_);
goto v___jp_488_;
}
else
{
lean_object* v_val_501_; lean_object* v_name_502_; lean_object* v_kind_503_; lean_object* v_config_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_val_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_val_501_);
lean_dec_ref(v___x_500_);
v_name_502_ = lean_ctor_get(v_val_501_, 1);
lean_inc(v_name_502_);
v_kind_503_ = lean_ctor_get(v_val_501_, 2);
lean_inc(v_kind_503_);
v_config_504_ = lean_ctor_get(v_val_501_, 3);
lean_inc(v_config_504_);
lean_dec(v_val_501_);
v___x_505_ = ((lean_object*)(l_Lake_Package_test___closed__4));
v___x_506_ = lean_name_eq(v_kind_503_, v___x_505_);
lean_dec(v_kind_503_);
if (v___x_506_ == 0)
{
lean_inc(v_baseName_476_);
lean_dec(v_config_504_);
lean_dec(v_name_502_);
lean_dec(v_keyName_477_);
lean_dec_ref(v_testDriverArgs_475_);
lean_dec(v_fst_473_);
lean_del_object(v___x_471_);
lean_dec_ref(v_buildConfig_462_);
lean_dec(v_args_461_);
goto v___jp_488_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
lean_dec(v_snd_474_);
v___x_507_ = lean_array_get_size(v_testDriverArgs_475_);
lean_dec_ref(v_testDriverArgs_475_);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_nat_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_inc(v_baseName_476_);
lean_dec(v_config_504_);
lean_dec(v_name_502_);
lean_dec(v_keyName_477_);
lean_dec(v_fst_473_);
lean_dec_ref(v_buildConfig_462_);
lean_dec(v_args_461_);
goto v___jp_479_;
}
else
{
uint8_t v___x_510_; 
v___x_510_ = l_List_isEmpty___redArg(v_args_461_);
lean_dec(v_args_461_);
if (v___x_510_ == 0)
{
lean_inc(v_baseName_476_);
lean_dec(v_config_504_);
lean_dec(v_name_502_);
lean_dec(v_keyName_477_);
lean_dec(v_fst_473_);
lean_dec_ref(v_buildConfig_462_);
goto v___jp_479_;
}
else
{
lean_object* v_toLogConfig_511_; uint8_t v_oldMode_512_; uint8_t v_trustHash_513_; uint8_t v_noBuild_514_; uint8_t v_verbosity_515_; uint8_t v_showSuccess_516_; lean_object* v_outputsFile_x3f_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_556_; 
lean_del_object(v___x_471_);
v_toLogConfig_511_ = lean_ctor_get(v_buildConfig_462_, 0);
v_oldMode_512_ = lean_ctor_get_uint8(v_buildConfig_462_, sizeof(void*)*2);
v_trustHash_513_ = lean_ctor_get_uint8(v_buildConfig_462_, sizeof(void*)*2 + 1);
v_noBuild_514_ = lean_ctor_get_uint8(v_buildConfig_462_, sizeof(void*)*2 + 2);
v_verbosity_515_ = lean_ctor_get_uint8(v_buildConfig_462_, sizeof(void*)*2 + 3);
v_showSuccess_516_ = lean_ctor_get_uint8(v_buildConfig_462_, sizeof(void*)*2 + 4);
v_outputsFile_x3f_517_ = lean_ctor_get(v_buildConfig_462_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_buildConfig_462_);
if (v_isSharedCheck_556_ == 0)
{
v___x_519_ = v_buildConfig_462_;
v_isShared_520_ = v_isSharedCheck_556_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_outputsFile_x3f_517_);
lean_inc(v_toLogConfig_511_);
lean_dec(v_buildConfig_462_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_556_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint8_t v_failLv_521_; uint8_t v_outLv_522_; uint8_t v_ansiMode_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_554_; 
v_failLv_521_ = lean_ctor_get_uint8(v_toLogConfig_511_, sizeof(void*)*1);
v_outLv_522_ = lean_ctor_get_uint8(v_toLogConfig_511_, sizeof(void*)*1 + 1);
v_ansiMode_523_ = lean_ctor_get_uint8(v_toLogConfig_511_, sizeof(void*)*1 + 2);
v_isSharedCheck_554_ = !lean_is_exclusive(v_toLogConfig_511_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_toLogConfig_511_, 0);
lean_dec(v_unused_555_);
v___x_525_ = v_toLogConfig_511_;
v_isShared_526_ = v_isSharedCheck_554_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_toLogConfig_511_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_554_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc(v_name_502_);
v___x_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_527_, 0, v_fst_473_);
lean_ctor_set(v___x_527_, 1, v_name_502_);
lean_ctor_set(v___x_527_, 2, v_config_504_);
v___f_528_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0___boxed), 11, 4);
lean_closure_set(v___f_528_, 0, v_keyName_477_);
lean_closure_set(v___f_528_, 1, v_name_502_);
lean_closure_set(v___f_528_, 2, v___x_505_);
lean_closure_set(v___f_528_, 3, v___x_527_);
v___x_529_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_529_);
v___x_531_ = v___x_525_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_529_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*1, v_failLv_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*1 + 1, v_outLv_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*1 + 2, v_ansiMode_523_);
v___x_531_ = v_reuseFailAlloc_553_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_531_);
v___x_533_ = v___x_519_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_outputsFile_x3f_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_552_, sizeof(void*)*2, v_oldMode_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_552_, sizeof(void*)*2 + 1, v_trustHash_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_552_, sizeof(void*)*2 + 2, v_noBuild_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_552_, sizeof(void*)*2 + 3, v_verbosity_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_552_, sizeof(void*)*2 + 4, v_showSuccess_516_);
v___x_533_ = v_reuseFailAlloc_552_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; 
lean_inc(v_a_463_);
v___x_534_ = l_Lake_Workspace_runBuild___redArg(v_a_463_, v___f_528_, v___x_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_542_; 
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v___x_534_, 0);
lean_dec(v_unused_543_);
v___x_536_ = v___x_534_;
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
else
{
lean_dec(v___x_534_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_542_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lake_Package_test___boxed__const__1;
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_534_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_534_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
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
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_config_465_);
lean_dec_ref(v_buildConfig_462_);
lean_dec(v_args_461_);
v_a_586_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_468_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_468_);
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
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed(lean_object* v_pkg_594_, lean_object* v_args_595_, lean_object* v_buildConfig_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lake_Package_test(v_pkg_594_, v_args_595_, v_buildConfig_596_, v_a_597_);
lean_dec(v_a_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object* v_pkg_602_, lean_object* v_args_603_, lean_object* v_buildConfig_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_config_607_; lean_object* v_lintDriver_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_config_607_ = lean_ctor_get(v_pkg_602_, 6);
lean_inc_ref(v_config_607_);
v_lintDriver_608_ = lean_ctor_get(v_pkg_602_, 22);
lean_inc_ref(v_lintDriver_608_);
v___x_609_ = ((lean_object*)(l_Lake_Package_lint___closed__0));
v___x_610_ = l_Lake_Package_resolveDriver(v_pkg_602_, v___x_609_, v_lintDriver_608_, v_a_605_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_661_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_661_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_661_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_661_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_fst_615_; lean_object* v_snd_616_; lean_object* v_lintDriverArgs_617_; lean_object* v_baseName_618_; lean_object* v_keyName_619_; lean_object* v_scripts_620_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_fst_615_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_fst_615_);
v_snd_616_ = lean_ctor_get(v_a_611_, 1);
lean_inc_n(v_snd_616_, 2);
lean_dec(v_a_611_);
v_lintDriverArgs_617_ = lean_ctor_get(v_config_607_, 15);
lean_inc_ref(v_lintDriverArgs_617_);
lean_dec_ref(v_config_607_);
v_baseName_618_ = lean_ctor_get(v_fst_615_, 1);
v_keyName_619_ = lean_ctor_get(v_fst_615_, 2);
lean_inc(v_keyName_619_);
v_scripts_620_ = lean_ctor_get(v_fst_615_, 17);
v___x_633_ = l_String_toName(v_snd_616_);
v___x_634_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_620_, v___x_633_);
if (lean_obj_tag(v___x_634_) == 1)
{
lean_object* v_val_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v___x_633_);
lean_dec(v_keyName_619_);
lean_dec(v_snd_616_);
lean_dec(v_fst_615_);
lean_del_object(v___x_613_);
lean_dec_ref(v_buildConfig_604_);
v_val_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_val_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = lean_array_to_list(v_lintDriverArgs_617_);
v___x_637_ = l_List_appendTR___redArg(v___x_636_, v_args_603_);
v___x_638_ = l_Lake_Script_run(v___x_637_, v_val_635_, v_a_605_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
lean_dec(v___x_634_);
v___x_639_ = l_Lake_Package_findTargetDecl_x3f(v___x_633_, v_fst_615_);
lean_dec(v___x_633_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_inc(v_baseName_618_);
lean_dec(v_keyName_619_);
lean_dec_ref(v_lintDriverArgs_617_);
lean_dec(v_fst_615_);
lean_dec_ref(v_buildConfig_604_);
lean_dec(v_args_603_);
goto v___jp_621_;
}
else
{
lean_object* v_val_640_; lean_object* v_name_641_; lean_object* v_kind_642_; lean_object* v_config_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref(v___x_639_);
v_name_641_ = lean_ctor_get(v_val_640_, 1);
lean_inc(v_name_641_);
v_kind_642_ = lean_ctor_get(v_val_640_, 2);
lean_inc(v_kind_642_);
v_config_643_ = lean_ctor_get(v_val_640_, 3);
lean_inc(v_config_643_);
lean_dec(v_val_640_);
v___x_644_ = l_Lake_LeanExe_keyword;
v___x_645_ = lean_name_eq(v_kind_642_, v___x_644_);
lean_dec(v_kind_642_);
if (v___x_645_ == 0)
{
lean_inc(v_baseName_618_);
lean_dec(v_config_643_);
lean_dec(v_name_641_);
lean_dec(v_keyName_619_);
lean_dec_ref(v_lintDriverArgs_617_);
lean_dec(v_fst_615_);
lean_dec_ref(v_buildConfig_604_);
lean_dec(v_args_603_);
goto v___jp_621_;
}
else
{
lean_object* v___x_646_; lean_object* v___f_647_; lean_object* v___x_648_; 
lean_dec(v_snd_616_);
lean_del_object(v___x_613_);
lean_inc(v_name_641_);
v___x_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_646_, 0, v_fst_615_);
lean_ctor_set(v___x_646_, 1, v_name_641_);
lean_ctor_set(v___x_646_, 2, v_config_643_);
v___f_647_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_647_, 0, v_keyName_619_);
lean_closure_set(v___f_647_, 1, v_name_641_);
lean_closure_set(v___f_647_, 2, v___x_644_);
lean_closure_set(v___f_647_, 3, v___x_646_);
lean_inc(v_a_605_);
v___x_648_ = l_Lake_Workspace_runBuild___redArg(v_a_605_, v___f_647_, v_buildConfig_604_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = lean_array_mk(v_args_603_);
v___x_651_ = l_Array_append___redArg(v_lintDriverArgs_617_, v___x_650_);
lean_dec_ref(v___x_650_);
v___x_652_ = l_Lake_env(v_a_649_, v___x_651_, v_a_605_);
return v___x_652_;
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v_lintDriverArgs_617_);
lean_dec(v_args_603_);
v_a_653_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_648_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_648_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
}
v___jp_621_:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_622_ = 0;
v___x_623_ = l_Lean_Name_toString(v_baseName_618_, v___x_622_);
v___x_624_ = ((lean_object*)(l_Lake_Package_lint___closed__1));
v___x_625_ = lean_string_append(v___x_623_, v___x_624_);
v___x_626_ = lean_string_append(v___x_625_, v_snd_616_);
lean_dec(v_snd_616_);
v___x_627_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_628_ = lean_string_append(v___x_626_, v___x_627_);
v___x_629_ = lean_mk_io_user_error(v___x_628_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 1);
lean_ctor_set(v___x_613_, 0, v___x_629_);
v___x_631_ = v___x_613_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_config_607_);
lean_dec_ref(v_buildConfig_604_);
lean_dec(v_args_603_);
v_a_662_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_610_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_610_);
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
LEAN_EXPORT lean_object* l_Lake_Package_lint___boxed(lean_object* v_pkg_670_, lean_object* v_args_671_, lean_object* v_buildConfig_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lake_Package_lint(v_pkg_670_, v_args_671_, v_buildConfig_672_, v_a_673_);
lean_dec(v_a_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object* v_ws_676_, lean_object* v_leanFile_677_, lean_object* v_moreArgs_678_, lean_object* v_buildConfig_679_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_alloc_closure((void*)(l_Lake_prepareLeanCommand___boxed), 9, 2);
lean_closure_set(v___x_681_, 0, v_leanFile_677_);
lean_closure_set(v___x_681_, 1, v_moreArgs_678_);
v___x_682_ = l_Lake_Workspace_runBuild___redArg(v_ws_676_, v___x_681_, v_buildConfig_679_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc_n(v_a_683_, 2);
lean_dec_ref(v___x_682_);
v___x_684_ = lean_io_process_spawn(v_a_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v_toStdioConfig_686_; lean_object* v___x_687_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v___x_684_);
v_toStdioConfig_686_ = lean_ctor_get(v_a_683_, 0);
lean_inc_ref(v_toStdioConfig_686_);
lean_dec(v_a_683_);
v___x_687_ = lean_io_process_child_wait(v_toStdioConfig_686_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_toStdioConfig_686_);
return v___x_687_;
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_a_683_);
v_a_688_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_684_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_684_);
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
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_682_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_682_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile___boxed(lean_object* v_ws_704_, lean_object* v_leanFile_705_, lean_object* v_moreArgs_706_, lean_object* v_buildConfig_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lake_Workspace_evalLeanFile(v_ws_704_, v_leanFile_705_, v_moreArgs_706_, v_buildConfig_707_);
return v_res_709_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Run(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Module(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
