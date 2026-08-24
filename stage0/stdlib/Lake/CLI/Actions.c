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
lean_object* v_currPos_249_; lean_object* v_searcher_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_273_; 
v_currPos_249_ = lean_ctor_get(v_a_239_, 0);
v_searcher_250_ = lean_ctor_get(v_a_239_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_a_239_);
if (v_isSharedCheck_273_ == 0)
{
v___x_252_ = v_a_239_;
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_searcher_250_);
lean_inc(v_currPos_249_);
lean_dec(v_a_239_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_273_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v_decide_254_; 
v_decide_254_ = lean_nat_dec_eq(v_searcher_250_, v___x_238_);
if (v_decide_254_ == 0)
{
uint32_t v___x_255_; uint32_t v___x_256_; uint8_t v___x_257_; 
v___x_255_ = 47;
v___x_256_ = lean_string_utf8_get_fast(v_driver_236_, v_searcher_250_);
v___x_257_ = lean_uint32_dec_eq(v___x_256_, v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_string_utf8_next_fast(v_driver_236_, v_searcher_250_);
lean_dec(v_searcher_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_258_);
v___x_260_ = v___x_252_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_currPos_249_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_262_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v_a_239_ = v___x_260_;
goto _start;
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_slice_266_; lean_object* v_nextIt_268_; 
v___x_263_ = lean_string_utf8_next_fast(v_driver_236_, v_searcher_250_);
v___x_264_ = lean_nat_sub(v___x_263_, v_searcher_250_);
v___x_265_ = lean_nat_add(v_searcher_250_, v___x_264_);
lean_dec(v___x_264_);
v_slice_266_ = l_String_Slice_subslice_x21(v___x_237_, v_currPos_249_, v_searcher_250_);
lean_inc(v___x_265_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_265_);
lean_ctor_set(v___x_252_, 0, v___x_265_);
v_nextIt_268_ = v___x_252_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_265_);
v_nextIt_268_ = v_reuseFailAlloc_271_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v_startInclusive_269_; lean_object* v_endExclusive_270_; 
v_startInclusive_269_ = lean_ctor_get(v_slice_266_, 0);
lean_inc(v_startInclusive_269_);
v_endExclusive_270_ = lean_ctor_get(v_slice_266_, 1);
lean_inc(v_endExclusive_270_);
lean_dec_ref(v_slice_266_);
v_it_242_ = v_nextIt_268_;
v_startInclusive_243_ = v_startInclusive_269_;
v_endExclusive_244_ = v_endExclusive_270_;
goto v___jp_241_;
}
}
}
else
{
lean_object* v___x_272_; 
lean_del_object(v___x_252_);
lean_dec(v_searcher_250_);
v___x_272_ = lean_box(1);
lean_inc(v___x_238_);
v_it_242_ = v___x_272_;
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
lean_dec_ref_known(v___x_245_, 3);
v___x_247_ = lean_array_push(v_b_240_, v___x_246_);
v_a_239_ = v_it_242_;
v_b_240_ = v___x_247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg___boxed(lean_object* v_driver_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_274_, v___x_275_, v___x_276_, v_a_277_, v_b_278_);
lean_dec_ref(v___x_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object* v_pkg_288_, lean_object* v_kind_289_, lean_object* v_driver_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = lean_string_utf8_byte_size(v_driver_290_);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_dec_eq(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc_ref_n(v_driver_290_, 2);
v___x_309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_309_, 0, v_driver_290_);
lean_ctor_set(v___x_309_, 1, v___x_294_);
lean_ctor_set(v___x_309_, 2, v___x_293_);
v___x_310_ = l_String_Slice_splitToSubslice___at___00Lake_Package_resolveDriver_spec__0(v___x_309_);
v___x_311_ = ((lean_object*)(l_Lake_Package_pack___closed__1));
v___x_312_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_290_, v___x_309_, v___x_293_, v___x_310_, v___x_311_);
lean_dec_ref_known(v___x_309_, 3);
v___x_313_ = lean_array_to_list(v___x_312_);
if (lean_obj_tag(v___x_313_) == 1)
{
lean_object* v_head_314_; lean_object* v_tail_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_362_; 
v_head_314_ = lean_ctor_get(v___x_313_, 0);
v_tail_315_ = lean_ctor_get(v___x_313_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_362_ == 0)
{
v___x_317_ = v___x_313_;
v_isShared_318_ = v_isSharedCheck_362_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_tail_315_);
lean_inc(v_head_314_);
lean_dec(v___x_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_362_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
if (lean_obj_tag(v_tail_315_) == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_driver_290_);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 0);
lean_ctor_set(v___x_317_, 1, v_head_314_);
lean_ctor_set(v___x_317_, 0, v_pkg_288_);
v___x_333_ = v___x_317_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_pkg_288_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_head_314_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
else
{
lean_object* v_tail_336_; 
lean_del_object(v___x_317_);
v_tail_336_ = lean_ctor_get(v_tail_315_, 1);
if (lean_obj_tag(v_tail_336_) == 0)
{
lean_object* v_head_337_; lean_object* v_packages_338_; lean_object* v___x_339_; lean_object* v___x_340_; size_t v_sz_341_; size_t v___x_342_; lean_object* v___x_343_; lean_object* v_fst_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v_driver_290_);
v_head_337_ = lean_ctor_get(v_tail_315_, 0);
lean_inc(v_head_337_);
lean_dec_ref_known(v_tail_315_, 2);
v_packages_338_ = lean_ctor_get(v_a_291_, 4);
lean_inc(v_head_314_);
v___x_339_ = l_String_toName(v_head_314_);
v___x_340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2___closed__0));
v_sz_341_ = lean_array_size(v_packages_338_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Package_resolveDriver_spec__2(v___x_339_, v_packages_338_, v_sz_341_, v___x_342_, v___x_340_);
lean_dec(v___x_339_);
v_fst_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v___x_343_, 1);
lean_dec(v_unused_361_);
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_360_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_fst_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_360_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
if (lean_obj_tag(v_fst_344_) == 0)
{
lean_del_object(v___x_346_);
lean_dec(v_head_337_);
goto v___jp_319_;
}
else
{
lean_object* v_val_348_; 
v_val_348_ = lean_ctor_get(v_fst_344_, 0);
lean_inc(v_val_348_);
lean_dec_ref_known(v_fst_344_, 1);
if (lean_obj_tag(v_val_348_) == 1)
{
lean_object* v_val_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_head_314_);
lean_dec_ref(v_pkg_288_);
v_val_349_ = lean_ctor_get(v_val_348_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_val_348_);
if (v_isSharedCheck_359_ == 0)
{
v___x_351_ = v_val_348_;
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_val_349_);
lean_dec(v_val_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_head_337_);
lean_ctor_set(v___x_346_, 0, v_val_349_);
v___x_354_ = v___x_346_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_val_349_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_head_337_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set_tag(v___x_351_, 0);
lean_ctor_set(v___x_351_, 0, v___x_354_);
v___x_356_ = v___x_351_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_dec(v_val_348_);
lean_del_object(v___x_346_);
lean_dec(v_head_337_);
goto v___jp_319_;
}
}
}
}
else
{
lean_dec_ref_known(v_tail_315_, 2);
lean_dec(v_head_314_);
goto v___jp_296_;
}
}
v___jp_319_:
{
lean_object* v_baseName_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_baseName_320_ = lean_ctor_get(v_pkg_288_, 1);
lean_inc(v_baseName_320_);
lean_dec_ref(v_pkg_288_);
v___x_321_ = l_Lean_Name_toString(v_baseName_320_, v___x_295_);
v___x_322_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__3));
v___x_323_ = lean_string_append(v___x_321_, v___x_322_);
v___x_324_ = lean_string_append(v___x_323_, v_kind_289_);
v___x_325_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__4));
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
v___x_327_ = lean_string_append(v___x_326_, v_head_314_);
lean_dec(v_head_314_);
v___x_328_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_329_ = lean_string_append(v___x_327_, v___x_328_);
v___x_330_ = lean_mk_io_user_error(v___x_329_);
v___x_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
}
else
{
lean_dec(v___x_313_);
goto v___jp_296_;
}
}
else
{
lean_object* v_baseName_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec_ref(v_driver_290_);
v_baseName_363_ = lean_ctor_get(v_pkg_288_, 1);
lean_inc(v_baseName_363_);
lean_dec_ref(v_pkg_288_);
v___x_364_ = 0;
v___x_365_ = l_Lean_Name_toString(v_baseName_363_, v___x_364_);
v___x_366_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__6));
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
v___x_368_ = lean_string_append(v___x_367_, v_kind_289_);
v___x_369_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__7));
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
v___x_371_ = lean_mk_io_user_error(v___x_370_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
v___jp_296_:
{
lean_object* v_baseName_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_baseName_297_ = lean_ctor_get(v_pkg_288_, 1);
lean_inc(v_baseName_297_);
lean_dec_ref(v_pkg_288_);
v___x_298_ = l_Lean_Name_toString(v_baseName_297_, v___x_295_);
v___x_299_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__0));
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
v___x_301_ = lean_string_append(v___x_300_, v_kind_289_);
v___x_302_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__1));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
v___x_304_ = lean_string_append(v___x_303_, v_driver_290_);
lean_dec_ref(v_driver_290_);
v___x_305_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__2));
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
v___x_307_ = lean_mk_io_user_error(v___x_306_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object* v_pkg_373_, lean_object* v_kind_374_, lean_object* v_driver_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lake_Package_resolveDriver(v_pkg_373_, v_kind_374_, v_driver_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_kind_374_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(lean_object* v_driver_379_, lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v_inst_382_, lean_object* v_R_383_, lean_object* v_a_384_, lean_object* v_b_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___redArg(v_driver_379_, v___x_380_, v___x_381_, v_a_384_, v_b_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1___boxed(lean_object* v_driver_387_, lean_object* v___x_388_, lean_object* v___x_389_, lean_object* v_inst_390_, lean_object* v_R_391_, lean_object* v_a_392_, lean_object* v_b_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Package_resolveDriver_spec__1(v_driver_387_, v___x_388_, v___x_389_, v_inst_390_, v_R_391_, v_a_392_, v_b_393_);
lean_dec_ref(v___x_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0(lean_object* v_keyName_395_, lean_object* v_name_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = l_Lake_LeanLib_defaultFacet;
v___x_407_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_407_, 0, v_keyName_395_);
lean_ctor_set(v___x_407_, 1, v_name_396_);
v___x_408_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_397_);
lean_ctor_set(v___x_408_, 2, v___x_398_);
lean_ctor_set(v___x_408_, 3, v___x_406_);
v___x_409_ = lean_apply_7(v___y_399_, v___x_408_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, lean_box(0));
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__0___boxed(lean_object* v_keyName_410_, lean_object* v_name_411_, lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lake_Package_test___lam__0(v_keyName_410_, v_name_411_, v___x_412_, v___x_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object* v_keyName_422_, lean_object* v_name_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = l_Lake_LeanExe_exeFacet;
v___x_434_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_434_, 0, v_keyName_422_);
lean_ctor_set(v___x_434_, 1, v_name_423_);
v___x_435_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_424_);
lean_ctor_set(v___x_435_, 2, v___x_425_);
lean_ctor_set(v___x_435_, 3, v___x_433_);
v___x_436_ = lean_apply_7(v___y_426_, v___x_435_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, lean_box(0));
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1___boxed(lean_object* v_keyName_437_, lean_object* v_name_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lake_Package_test___lam__1(v_keyName_437_, v_name_438_, v___x_439_, v___x_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v_res_448_;
}
}
static lean_object* _init_l_Lake_Package_test___boxed__const__1(void){
_start:
{
uint32_t v___x_455_; lean_object* v___x_456_; 
v___x_455_ = 0;
v___x_456_ = lean_box_uint32(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* v_pkg_457_, lean_object* v_args_458_, lean_object* v_buildConfig_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_config_462_; lean_object* v_testDriver_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_config_462_ = lean_ctor_get(v_pkg_457_, 6);
lean_inc_ref(v_config_462_);
v_testDriver_463_ = lean_ctor_get(v_pkg_457_, 22);
lean_inc_ref(v_testDriver_463_);
v___x_464_ = ((lean_object*)(l_Lake_Package_test___closed__0));
v___x_465_ = l_Lake_Package_resolveDriver(v_pkg_457_, v___x_464_, v_testDriver_463_, v_a_460_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_588_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_588_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_588_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_588_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v_testDriverArgs_472_; lean_object* v_baseName_473_; lean_object* v_keyName_474_; lean_object* v_scripts_475_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; uint8_t v___y_481_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_fst_470_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v_a_466_, 1);
lean_inc_n(v_snd_471_, 2);
lean_dec(v_a_466_);
v_testDriverArgs_472_ = lean_ctor_get(v_config_462_, 13);
lean_inc_ref(v_testDriverArgs_472_);
lean_dec_ref(v_config_462_);
v_baseName_473_ = lean_ctor_get(v_fst_470_, 1);
v_keyName_474_ = lean_ctor_get(v_fst_470_, 2);
lean_inc(v_keyName_474_);
v_scripts_475_ = lean_ctor_get(v_fst_470_, 18);
v___x_560_ = l_String_toName(v_snd_471_);
v___x_561_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_475_, v___x_560_);
if (lean_obj_tag(v___x_561_) == 1)
{
lean_object* v_val_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec(v___x_560_);
lean_dec(v_keyName_474_);
lean_dec(v_snd_471_);
lean_dec(v_fst_470_);
lean_del_object(v___x_468_);
lean_dec_ref(v_buildConfig_459_);
v_val_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_val_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = lean_array_to_list(v_testDriverArgs_472_);
v___x_564_ = l_List_appendTR___redArg(v___x_563_, v_args_458_);
v___x_565_ = l_Lake_Script_run(v___x_564_, v_val_562_, v_a_460_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; 
lean_dec(v___x_561_);
v___x_566_ = l_Lake_Package_findTargetDecl_x3f(v___x_560_, v_fst_470_);
lean_dec(v___x_560_);
if (lean_obj_tag(v___x_566_) == 0)
{
goto v___jp_547_;
}
else
{
lean_object* v_val_567_; lean_object* v_name_568_; lean_object* v_kind_569_; lean_object* v_config_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_val_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_566_, 1);
v_name_568_ = lean_ctor_get(v_val_567_, 1);
lean_inc(v_name_568_);
v_kind_569_ = lean_ctor_get(v_val_567_, 2);
lean_inc(v_kind_569_);
v_config_570_ = lean_ctor_get(v_val_567_, 3);
lean_inc(v_config_570_);
lean_dec(v_val_567_);
v___x_571_ = l_Lake_LeanExe_keyword;
v___x_572_ = lean_name_eq(v_kind_569_, v___x_571_);
lean_dec(v_kind_569_);
if (v___x_572_ == 0)
{
lean_dec(v_config_570_);
lean_dec(v_name_568_);
goto v___jp_547_;
}
else
{
lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___x_575_; 
lean_dec(v_snd_471_);
lean_del_object(v___x_468_);
lean_inc(v_name_568_);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v_fst_470_);
lean_ctor_set(v___x_573_, 1, v_name_568_);
lean_ctor_set(v___x_573_, 2, v_config_570_);
v___f_574_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_574_, 0, v_keyName_474_);
lean_closure_set(v___f_574_, 1, v_name_568_);
lean_closure_set(v___f_574_, 2, v___x_571_);
lean_closure_set(v___f_574_, 3, v___x_573_);
lean_inc(v_a_460_);
v___x_575_ = l_Lake_Workspace_runBuild___redArg(v_a_460_, v___f_574_, v_buildConfig_459_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = lean_array_mk(v_args_458_);
v___x_578_ = l_Array_append___redArg(v_testDriverArgs_472_, v___x_577_);
lean_dec_ref(v___x_577_);
v___x_579_ = l_Lake_env(v_a_576_, v___x_578_, v_a_460_);
return v___x_579_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_testDriverArgs_472_);
lean_dec(v_args_458_);
v_a_580_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_575_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_575_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
v___jp_476_:
{
if (v___y_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
lean_inc(v_baseName_473_);
lean_dec(v___y_480_);
lean_dec(v___y_479_);
lean_dec(v___y_477_);
lean_dec(v_keyName_474_);
lean_dec(v_fst_470_);
lean_dec_ref(v_buildConfig_459_);
v___x_482_ = l_Lean_Name_toString(v_baseName_473_, v___y_481_);
v___x_483_ = ((lean_object*)(l_Lake_Package_test___closed__1));
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
v___x_485_ = lean_mk_io_user_error(v___x_484_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 1);
lean_ctor_set(v___x_468_, 0, v___x_485_);
v___x_487_ = v___x_468_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v_toLogConfig_489_; uint8_t v_oldMode_490_; uint8_t v_trustHash_491_; uint8_t v_noBuild_492_; uint8_t v_verbosity_493_; uint8_t v_showSuccess_494_; lean_object* v_outputsFile_x3f_495_; lean_object* v_leanOptOverrides_496_; lean_object* v_macosxDeploymentTarget_x3f_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_536_; 
lean_del_object(v___x_468_);
v_toLogConfig_489_ = lean_ctor_get(v_buildConfig_459_, 0);
v_oldMode_490_ = lean_ctor_get_uint8(v_buildConfig_459_, sizeof(void*)*4);
v_trustHash_491_ = lean_ctor_get_uint8(v_buildConfig_459_, sizeof(void*)*4 + 1);
v_noBuild_492_ = lean_ctor_get_uint8(v_buildConfig_459_, sizeof(void*)*4 + 2);
v_verbosity_493_ = lean_ctor_get_uint8(v_buildConfig_459_, sizeof(void*)*4 + 3);
v_showSuccess_494_ = lean_ctor_get_uint8(v_buildConfig_459_, sizeof(void*)*4 + 4);
v_outputsFile_x3f_495_ = lean_ctor_get(v_buildConfig_459_, 1);
v_leanOptOverrides_496_ = lean_ctor_get(v_buildConfig_459_, 2);
v_macosxDeploymentTarget_x3f_497_ = lean_ctor_get(v_buildConfig_459_, 3);
v_isSharedCheck_536_ = !lean_is_exclusive(v_buildConfig_459_);
if (v_isSharedCheck_536_ == 0)
{
v___x_499_ = v_buildConfig_459_;
v_isShared_500_ = v_isSharedCheck_536_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_macosxDeploymentTarget_x3f_497_);
lean_inc(v_leanOptOverrides_496_);
lean_inc(v_outputsFile_x3f_495_);
lean_inc(v_toLogConfig_489_);
lean_dec(v_buildConfig_459_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_536_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v_failLv_501_; uint8_t v_outLv_502_; uint8_t v_ansiMode_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_534_; 
v_failLv_501_ = lean_ctor_get_uint8(v_toLogConfig_489_, sizeof(void*)*1);
v_outLv_502_ = lean_ctor_get_uint8(v_toLogConfig_489_, sizeof(void*)*1 + 1);
v_ansiMode_503_ = lean_ctor_get_uint8(v_toLogConfig_489_, sizeof(void*)*1 + 2);
v_isSharedCheck_534_ = !lean_is_exclusive(v_toLogConfig_489_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_toLogConfig_489_, 0);
lean_dec(v_unused_535_);
v___x_505_ = v_toLogConfig_489_;
v_isShared_506_ = v_isSharedCheck_534_;
goto v_resetjp_504_;
}
else
{
lean_dec(v_toLogConfig_489_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_534_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v_fst_470_);
lean_ctor_set(v___x_507_, 1, v___y_480_);
lean_ctor_set(v___x_507_, 2, v___y_479_);
lean_inc(v___y_478_);
v___f_508_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__0___boxed), 11, 4);
lean_closure_set(v___f_508_, 0, v_keyName_474_);
lean_closure_set(v___f_508_, 1, v___y_477_);
lean_closure_set(v___f_508_, 2, v___y_478_);
lean_closure_set(v___f_508_, 3, v___x_507_);
v___x_509_ = lean_box(0);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_509_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*1, v_failLv_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*1 + 1, v_outLv_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_533_, sizeof(void*)*1 + 2, v_ansiMode_503_);
v___x_511_ = v_reuseFailAlloc_533_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_511_);
v___x_513_ = v___x_499_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_outputsFile_x3f_495_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_leanOptOverrides_496_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_macosxDeploymentTarget_x3f_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*4, v_oldMode_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*4 + 1, v_trustHash_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*4 + 2, v_noBuild_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*4 + 3, v_verbosity_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_532_, sizeof(void*)*4 + 4, v_showSuccess_494_);
v___x_513_ = v_reuseFailAlloc_532_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
lean_inc(v_a_460_);
v___x_514_ = l_Lake_Workspace_runBuild___redArg(v_a_460_, v___f_508_, v___x_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_514_, 0);
lean_dec(v_unused_523_);
v___x_516_ = v___x_514_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_dec(v___x_514_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = l_Lake_Package_test___boxed__const__1;
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_514_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
}
}
}
}
v___jp_537_:
{
uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_538_ = 0;
v___x_539_ = l_Lean_Name_toString(v_baseName_473_, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lake_Package_test___closed__2));
v___x_541_ = lean_string_append(v___x_539_, v___x_540_);
v___x_542_ = lean_string_append(v___x_541_, v_snd_471_);
lean_dec(v_snd_471_);
v___x_543_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v___x_545_ = lean_mk_io_user_error(v___x_544_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
v___jp_547_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_inc(v_snd_471_);
v___x_548_ = l_String_toName(v_snd_471_);
v___x_549_ = l_Lake_Package_findTargetDecl_x3f(v___x_548_, v_fst_470_);
lean_dec(v___x_548_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_inc(v_baseName_473_);
lean_dec(v_keyName_474_);
lean_dec_ref(v_testDriverArgs_472_);
lean_dec(v_fst_470_);
lean_del_object(v___x_468_);
lean_dec_ref(v_buildConfig_459_);
lean_dec(v_args_458_);
goto v___jp_537_;
}
else
{
lean_object* v_val_550_; lean_object* v_name_551_; lean_object* v_kind_552_; lean_object* v_config_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_val_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v___x_549_, 1);
v_name_551_ = lean_ctor_get(v_val_550_, 1);
lean_inc(v_name_551_);
v_kind_552_ = lean_ctor_get(v_val_550_, 2);
lean_inc(v_kind_552_);
v_config_553_ = lean_ctor_get(v_val_550_, 3);
lean_inc(v_config_553_);
lean_dec(v_val_550_);
v___x_554_ = ((lean_object*)(l_Lake_Package_test___closed__4));
v___x_555_ = lean_name_eq(v_kind_552_, v___x_554_);
lean_dec(v_kind_552_);
if (v___x_555_ == 0)
{
lean_inc(v_baseName_473_);
lean_dec(v_config_553_);
lean_dec(v_name_551_);
lean_dec(v_keyName_474_);
lean_dec_ref(v_testDriverArgs_472_);
lean_dec(v_fst_470_);
lean_del_object(v___x_468_);
lean_dec_ref(v_buildConfig_459_);
lean_dec(v_args_458_);
goto v___jp_537_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
lean_dec(v_snd_471_);
v___x_556_ = lean_array_get_size(v_testDriverArgs_472_);
lean_dec_ref(v_testDriverArgs_472_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_nat_dec_eq(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_args_458_);
lean_inc(v_name_551_);
v___y_477_ = v_name_551_;
v___y_478_ = v___x_554_;
v___y_479_ = v_config_553_;
v___y_480_ = v_name_551_;
v___y_481_ = v___x_558_;
goto v___jp_476_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = l_List_isEmpty___redArg(v_args_458_);
lean_dec(v_args_458_);
lean_inc(v_name_551_);
v___y_477_ = v_name_551_;
v___y_478_ = v___x_554_;
v___y_479_ = v_config_553_;
v___y_480_ = v_name_551_;
v___y_481_ = v___x_559_;
goto v___jp_476_;
}
}
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_config_462_);
lean_dec_ref(v_buildConfig_459_);
lean_dec(v_args_458_);
v_a_589_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_465_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_465_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___boxed(lean_object* v_pkg_597_, lean_object* v_args_598_, lean_object* v_buildConfig_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lake_Package_test(v_pkg_597_, v_args_598_, v_buildConfig_599_, v_a_600_);
lean_dec(v_a_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object* v_pkg_605_, lean_object* v_args_606_, lean_object* v_buildConfig_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_config_610_; lean_object* v_lintDriver_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_config_610_ = lean_ctor_get(v_pkg_605_, 6);
lean_inc_ref(v_config_610_);
v_lintDriver_611_ = lean_ctor_get(v_pkg_605_, 23);
lean_inc_ref(v_lintDriver_611_);
v___x_612_ = ((lean_object*)(l_Lake_Package_lint___closed__0));
v___x_613_ = l_Lake_Package_resolveDriver(v_pkg_605_, v___x_612_, v_lintDriver_611_, v_a_608_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_664_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_664_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_664_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_664_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v_lintDriverArgs_620_; lean_object* v_baseName_621_; lean_object* v_keyName_622_; lean_object* v_scripts_623_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_fst_618_ = lean_ctor_get(v_a_614_, 0);
lean_inc(v_fst_618_);
v_snd_619_ = lean_ctor_get(v_a_614_, 1);
lean_inc_n(v_snd_619_, 2);
lean_dec(v_a_614_);
v_lintDriverArgs_620_ = lean_ctor_get(v_config_610_, 15);
lean_inc_ref(v_lintDriverArgs_620_);
lean_dec_ref(v_config_610_);
v_baseName_621_ = lean_ctor_get(v_fst_618_, 1);
v_keyName_622_ = lean_ctor_get(v_fst_618_, 2);
lean_inc(v_keyName_622_);
v_scripts_623_ = lean_ctor_get(v_fst_618_, 18);
v___x_636_ = l_String_toName(v_snd_619_);
v___x_637_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_623_, v___x_636_);
if (lean_obj_tag(v___x_637_) == 1)
{
lean_object* v_val_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v___x_636_);
lean_dec(v_keyName_622_);
lean_dec(v_snd_619_);
lean_dec(v_fst_618_);
lean_del_object(v___x_616_);
lean_dec_ref(v_buildConfig_607_);
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_array_to_list(v_lintDriverArgs_620_);
v___x_640_ = l_List_appendTR___redArg(v___x_639_, v_args_606_);
v___x_641_ = l_Lake_Script_run(v___x_640_, v_val_638_, v_a_608_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; 
lean_dec(v___x_637_);
v___x_642_ = l_Lake_Package_findTargetDecl_x3f(v___x_636_, v_fst_618_);
lean_dec(v___x_636_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_inc(v_baseName_621_);
lean_dec(v_keyName_622_);
lean_dec_ref(v_lintDriverArgs_620_);
lean_dec(v_fst_618_);
lean_dec_ref(v_buildConfig_607_);
lean_dec(v_args_606_);
goto v___jp_624_;
}
else
{
lean_object* v_val_643_; lean_object* v_name_644_; lean_object* v_kind_645_; lean_object* v_config_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_val_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v___x_642_, 1);
v_name_644_ = lean_ctor_get(v_val_643_, 1);
lean_inc(v_name_644_);
v_kind_645_ = lean_ctor_get(v_val_643_, 2);
lean_inc(v_kind_645_);
v_config_646_ = lean_ctor_get(v_val_643_, 3);
lean_inc(v_config_646_);
lean_dec(v_val_643_);
v___x_647_ = l_Lake_LeanExe_keyword;
v___x_648_ = lean_name_eq(v_kind_645_, v___x_647_);
lean_dec(v_kind_645_);
if (v___x_648_ == 0)
{
lean_inc(v_baseName_621_);
lean_dec(v_config_646_);
lean_dec(v_name_644_);
lean_dec(v_keyName_622_);
lean_dec_ref(v_lintDriverArgs_620_);
lean_dec(v_fst_618_);
lean_dec_ref(v_buildConfig_607_);
lean_dec(v_args_606_);
goto v___jp_624_;
}
else
{
lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; 
lean_dec(v_snd_619_);
lean_del_object(v___x_616_);
lean_inc(v_name_644_);
v___x_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_649_, 0, v_fst_618_);
lean_ctor_set(v___x_649_, 1, v_name_644_);
lean_ctor_set(v___x_649_, 2, v_config_646_);
v___f_650_ = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1___boxed), 11, 4);
lean_closure_set(v___f_650_, 0, v_keyName_622_);
lean_closure_set(v___f_650_, 1, v_name_644_);
lean_closure_set(v___f_650_, 2, v___x_647_);
lean_closure_set(v___f_650_, 3, v___x_649_);
lean_inc(v_a_608_);
v___x_651_ = l_Lake_Workspace_runBuild___redArg(v_a_608_, v___f_650_, v_buildConfig_607_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = lean_array_mk(v_args_606_);
v___x_654_ = l_Array_append___redArg(v_lintDriverArgs_620_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = l_Lake_env(v_a_652_, v___x_654_, v_a_608_);
return v___x_655_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v_lintDriverArgs_620_);
lean_dec(v_args_606_);
v_a_656_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_651_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_651_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
v___jp_624_:
{
uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_625_ = 0;
v___x_626_ = l_Lean_Name_toString(v_baseName_621_, v___x_625_);
v___x_627_ = ((lean_object*)(l_Lake_Package_lint___closed__1));
v___x_628_ = lean_string_append(v___x_626_, v___x_627_);
v___x_629_ = lean_string_append(v___x_628_, v_snd_619_);
lean_dec(v_snd_619_);
v___x_630_ = ((lean_object*)(l_Lake_Package_resolveDriver___closed__5));
v___x_631_ = lean_string_append(v___x_629_, v___x_630_);
v___x_632_ = lean_mk_io_user_error(v___x_631_);
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 1);
lean_ctor_set(v___x_616_, 0, v___x_632_);
v___x_634_ = v___x_616_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_config_610_);
lean_dec_ref(v_buildConfig_607_);
lean_dec(v_args_606_);
v_a_665_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_613_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_613_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint___boxed(lean_object* v_pkg_673_, lean_object* v_args_674_, lean_object* v_buildConfig_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lake_Package_lint(v_pkg_673_, v_args_674_, v_buildConfig_675_, v_a_676_);
lean_dec(v_a_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile(lean_object* v_ws_679_, lean_object* v_leanFile_680_, lean_object* v_moreArgs_681_, lean_object* v_buildConfig_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_alloc_closure((void*)(l_Lake_prepareLeanCommand___boxed), 9, 2);
lean_closure_set(v___x_684_, 0, v_leanFile_680_);
lean_closure_set(v___x_684_, 1, v_moreArgs_681_);
v___x_685_ = l_Lake_Workspace_runBuild___redArg(v_ws_679_, v___x_684_, v_buildConfig_682_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc_n(v_a_686_, 2);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = lean_io_process_spawn(v_a_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v_toStdioConfig_689_; lean_object* v___x_690_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v_toStdioConfig_689_ = lean_ctor_get(v_a_686_, 0);
lean_inc_ref(v_toStdioConfig_689_);
lean_dec(v_a_686_);
v___x_690_ = lean_io_process_child_wait(v_toStdioConfig_689_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_toStdioConfig_689_);
return v___x_690_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_a_686_);
v_a_691_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_687_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
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
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_685_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_685_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_evalLeanFile___boxed(lean_object* v_ws_707_, lean_object* v_leanFile_708_, lean_object* v_moreArgs_709_, lean_object* v_buildConfig_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lake_Workspace_evalLeanFile(v_ws_707_, v_leanFile_708_, v_moreArgs_709_, v_buildConfig_710_);
return v_res_712_;
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
