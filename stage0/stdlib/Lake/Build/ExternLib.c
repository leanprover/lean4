// Lean compiler output
// Module: Lake.Build.ExternLib
// Imports: public import Lake.Config.FacetConfig public import Lake.Build.Job.Monad import Lake.Build.Job.Register import Lake.Build.Common import Lake.Build.Infos
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
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Lake_platformTrace;
extern lean_object* l_Lake_sharedLibExt;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isOSX;
lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
extern lean_object* l_Lake_ExternLib_defaultFacet;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_sharedFacet;
extern lean_object* l_Lake_ExternLib_dynlibFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "static"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0_value;
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ":static"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_ExternLib_staticFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ExternLib_staticFacetConfig___closed__0 = (const lean_object*)&l_Lake_ExternLib_staticFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_ExternLib_staticFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ExternLib_staticFacetConfig___closed__1 = (const lean_object*)&l_Lake_ExternLib_staticFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_ExternLib_staticFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_staticFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacetConfig;
static const lean_string_object l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0 = (const lean_object*)&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0_value;
static lean_once_cell_t l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1;
static const lean_string_object l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "-Wl,--whole-archive"};
static const lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2 = (const lean_object*)&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2_value;
static const lean_string_object l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-Wl,--no-whole-archive"};
static const lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3 = (const lean_object*)&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3_value;
static lean_once_cell_t l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4;
static const lean_string_object l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "-Wl,-force_load,"};
static const lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5 = (const lean_object*)&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(lean_object*);
static const lean_string_object l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "pure: "};
static const lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0 = (const lean_object*)&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0_value;
static const lean_string_object l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1 = (const lean_object*)&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1_value;
static const lean_array_object l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2 = (const lean_object*)&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2_value;
static lean_once_cell_t l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3;
static lean_once_cell_t l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ":shared"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ExternLib_sharedFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ExternLib_sharedFacetConfig___closed__0 = (const lean_object*)&l_Lake_ExternLib_sharedFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_ExternLib_sharedFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_sharedFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedFacetConfig;
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shared library `"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "` does not start with `lib`; this is not supported on Unix"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1_value;
static const lean_array_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4;
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` has no file name"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ":dynlib"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_ExternLib_dynlibFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ExternLib_dynlibFacetConfig___closed__0 = (const lean_object*)&l_Lake_ExternLib_dynlibFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_ExternLib_dynlibFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ExternLib_dynlibFacetConfig___closed__1 = (const lean_object*)&l_Lake_ExternLib_dynlibFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_ExternLib_dynlibFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_dynlibFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacetConfig;
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_ExternLib_defaultFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ExternLib_defaultFacetConfig___closed__0 = (const lean_object*)&l_Lake_ExternLib_defaultFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_ExternLib_defaultFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_defaultFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_ExternLib_defaultFacetConfig;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_ExternLib_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__0;
static lean_once_cell_t l_Lake_ExternLib_initFacetConfigs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__1;
static lean_once_cell_t l_Lake_ExternLib_initFacetConfigs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__2;
static lean_once_cell_t l_Lake_ExternLib_initFacetConfigs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ExternLib_initFacetConfigs___closed__3;
LEAN_EXPORT lean_object* l_Lake_ExternLib_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(lean_object* v___x_1_, lean_object* v_config_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc(v___y_5_);
lean_inc(v___y_4_);
v___x_10_ = lean_apply_7(v___y_3_, v___x_1_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, lean_box(0));
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v_a_11_; lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_20_; 
v_a_11_ = lean_ctor_get(v___x_10_, 0);
v_a_12_ = lean_ctor_get(v___x_10_, 1);
v_isSharedCheck_20_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_20_ == 0)
{
v___x_14_ = v___x_10_;
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_inc(v_a_11_);
lean_dec(v___x_10_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; lean_object* v___x_18_; 
v___x_16_ = lean_apply_1(v_config_2_, v_a_11_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v___x_16_);
v___x_18_ = v___x_14_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v___x_16_);
lean_ctor_set(v_reuseFailAlloc_19_, 1, v_a_12_);
v___x_18_ = v_reuseFailAlloc_19_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
return v___x_18_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_config_2_);
v_a_21_ = lean_ctor_get(v___x_10_, 0);
v_a_22_ = lean_ctor_get(v___x_10_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v___x_10_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_inc(v_a_21_);
lean_dec(v___x_10_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_21_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_a_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed(lean_object* v___x_30_, lean_object* v_config_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(v___x_30_, v_config_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec(v___y_34_);
lean_dec(v___y_33_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(lean_object* v_lib_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_pkg_50_; lean_object* v_name_51_; lean_object* v_config_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___f_59_; lean_object* v___x_60_; 
v_pkg_50_ = lean_ctor_get(v_lib_42_, 0);
lean_inc_ref(v_pkg_50_);
v_name_51_ = lean_ctor_get(v_lib_42_, 1);
lean_inc(v_name_51_);
v_config_52_ = lean_ctor_get(v_lib_42_, 2);
lean_inc(v_config_52_);
lean_dec_ref(v_lib_42_);
v___x_53_ = l_Lake_instDataKindFilePath;
v___x_54_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_55_ = l_Lean_Name_str___override(v_name_51_, v___x_54_);
v___x_56_ = 1;
lean_inc(v___x_55_);
v___x_57_ = l_Lean_Name_toString(v___x_55_, v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v_pkg_50_);
lean_ctor_set(v___x_58_, 1, v___x_55_);
v___f_59_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed), 9, 2);
lean_closure_set(v___f_59_, 0, v___x_58_);
lean_closure_set(v___f_59_, 1, v_config_52_);
v___x_60_ = l_Lake_ensureJob___redArg(v___x_53_, v___f_59_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_88_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_a_62_ = lean_ctor_get(v___x_60_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_88_ == 0)
{
v___x_64_ = v___x_60_;
v_isShared_65_ = v_isSharedCheck_88_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_88_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v_task_66_; lean_object* v_kind_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_86_; 
v_task_66_ = lean_ctor_get(v_a_61_, 0);
v_kind_67_ = lean_ctor_get(v_a_61_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_86_ == 0)
{
lean_object* v_unused_87_; 
v_unused_87_ = lean_ctor_get(v_a_61_, 2);
lean_dec(v_unused_87_);
v___x_69_ = v_a_61_;
v_isShared_70_ = v_isSharedCheck_86_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_kind_67_);
lean_inc(v_task_66_);
lean_dec(v_a_61_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_86_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_registeredJobs_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v_job_77_; 
v_registeredJobs_71_ = lean_ctor_get(v_a_47_, 3);
v___x_72_ = lean_st_ref_take(v_registeredJobs_71_);
v___x_73_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1));
v___x_74_ = lean_string_append(v___x_57_, v___x_73_);
v___x_75_ = 0;
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 2, v___x_74_);
v_job_77_ = v___x_69_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_task_66_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_kind_67_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v___x_74_);
v_job_77_ = v_reuseFailAlloc_85_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
lean_ctor_set_uint8(v_job_77_, sizeof(void*)*3, v___x_75_);
lean_inc_ref(v_job_77_);
v___x_78_ = l_Lake_Job_toOpaque___redArg(v_job_77_);
v___x_79_ = lean_array_push(v___x_72_, v___x_78_);
v___x_80_ = lean_st_ref_set(v_registeredJobs_71_, v___x_79_);
v___x_81_ = l_Lake_Job_renew___redArg(v_job_77_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_81_);
v___x_83_ = v___x_64_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_a_62_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_57_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed(lean_object* v_lib_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(v_lib_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec(v_a_92_);
lean_dec(v_a_91_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(uint8_t v_fmt_98_, lean_object* v_a_99_){
_start:
{
if (v_fmt_98_ == 0)
{
return v_a_99_;
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = l_Lake_mkRelPathString(v_a_99_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = l_Lean_Json_compress(v___x_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed(lean_object* v_fmt_103_, lean_object* v_a_104_){
_start:
{
uint8_t v_fmt_boxed_105_; lean_object* v_res_106_; 
v_fmt_boxed_105_ = lean_unbox(v_fmt_103_);
v_res_106_ = l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(v_fmt_boxed_105_, v_a_104_);
return v_res_106_;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___f_109_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_110_ = 1;
v___x_111_ = l_Lake_instDataKindFilePath;
v___x_112_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__1));
v___x_113_ = l_Lake_ExternLib_keyword;
v___x_114_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_111_);
lean_ctor_set(v___x_114_, 3, v___f_109_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*4, v___x_110_);
lean_ctor_set_uint8(v___x_114_, sizeof(void*)*4 + 1, v___x_110_);
return v___x_114_;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lake_ExternLib_staticFacetConfig___closed__2, &l_Lake_ExternLib_staticFacetConfig___closed__2_once, _init_l_Lake_ExternLib_staticFacetConfig___closed__2);
return v___x_115_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0));
v___x_118_ = lean_unsigned_to_nat(2u);
v___x_119_ = lean_mk_empty_array_with_capacity(v___x_118_);
v___x_120_ = lean_array_push(v___x_119_, v___x_117_);
return v___x_120_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2));
v___x_124_ = lean_unsigned_to_nat(3u);
v___x_125_ = lean_mk_empty_array_with_capacity(v___x_124_);
v___x_126_ = lean_array_push(v___x_125_, v___x_123_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0(lean_object* v_weakArgs_128_, lean_object* v_traceArgs_129_, lean_object* v___x_130_, lean_object* v_staticLib_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_toContext_139_; lean_object* v_lakeEnv_140_; lean_object* v_log_141_; uint8_t v_action_142_; uint8_t v_wantsRebuild_143_; lean_object* v_trace_144_; lean_object* v_buildTime_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_197_; 
v_toContext_139_ = lean_ctor_get(v___y_136_, 1);
v_lakeEnv_140_ = lean_ctor_get(v_toContext_139_, 0);
v_log_141_ = lean_ctor_get(v___y_137_, 0);
v_action_142_ = lean_ctor_get_uint8(v___y_137_, sizeof(void*)*3);
v_wantsRebuild_143_ = lean_ctor_get_uint8(v___y_137_, sizeof(void*)*3 + 1);
v_trace_144_ = lean_ctor_get(v___y_137_, 1);
v_buildTime_145_ = lean_ctor_get(v___y_137_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v___y_137_);
if (v_isSharedCheck_197_ == 0)
{
v___x_147_ = v___y_137_;
v_isShared_148_ = v_isSharedCheck_197_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_buildTime_145_);
lean_inc(v_trace_144_);
lean_inc(v_log_141_);
lean_dec(v___y_137_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_197_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_lean_149_; lean_object* v___y_151_; uint8_t v___x_187_; 
v_lean_149_ = lean_ctor_get(v_lakeEnv_140_, 1);
v___x_187_ = l_System_Platform_isOSX;
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3));
v___x_189_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4);
v___x_190_ = lean_array_push(v___x_189_, v_staticLib_131_);
v___x_191_ = lean_array_push(v___x_190_, v___x_188_);
v___y_151_ = v___x_191_;
goto v___jp_150_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5));
v___x_193_ = lean_string_append(v___x_192_, v_staticLib_131_);
lean_dec_ref(v_staticLib_131_);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_mk_empty_array_with_capacity(v___x_194_);
v___x_196_ = lean_array_push(v___x_195_, v___x_193_);
v___y_151_ = v___x_196_;
goto v___jp_150_;
}
v___jp_150_:
{
lean_object* v_leanLibDir_152_; lean_object* v_cc_153_; lean_object* v_ccLinkSharedFlags_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_leanLibDir_152_ = lean_ctor_get(v_lean_149_, 3);
v_cc_153_ = lean_ctor_get(v_lean_149_, 14);
v_ccLinkSharedFlags_154_ = lean_ctor_get(v_lean_149_, 20);
v___x_155_ = l_Array_append___redArg(v___y_151_, v_weakArgs_128_);
v___x_156_ = l_Array_append___redArg(v___x_155_, v_traceArgs_129_);
v___x_157_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1);
lean_inc_ref(v_leanLibDir_152_);
v___x_158_ = lean_array_push(v___x_157_, v_leanLibDir_152_);
v___x_159_ = l_Array_append___redArg(v___x_156_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = l_Array_append___redArg(v___x_159_, v_ccLinkSharedFlags_154_);
v___x_161_ = lean_box(0);
lean_inc_ref(v_cc_153_);
v___x_162_ = l_Lake_compileSharedLib(v___x_130_, v___x_160_, v_cc_153_, v___x_161_, v_log_141_);
lean_dec_ref(v___x_160_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_174_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_a_164_ = lean_ctor_get(v___x_162_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_174_ == 0)
{
v___x_166_ = v___x_162_;
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_a_164_);
v___x_169_ = v___x_147_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_164_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_trace_144_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_buildTime_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*3, v_action_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*3 + 1, v_wantsRebuild_143_);
v___x_169_ = v_reuseFailAlloc_173_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_169_);
v___x_171_ = v___x_166_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_163_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
v_a_175_ = lean_ctor_get(v___x_162_, 0);
v_a_176_ = lean_ctor_get(v___x_162_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v___x_162_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_inc(v_a_175_);
lean_dec(v___x_162_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_a_176_);
v___x_181_ = v___x_147_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_176_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_trace_144_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_buildTime_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, sizeof(void*)*3, v_action_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_185_, sizeof(void*)*3 + 1, v_wantsRebuild_143_);
v___x_181_ = v_reuseFailAlloc_185_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_181_);
v___x_183_ = v___x_178_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object* v_weakArgs_198_, lean_object* v_traceArgs_199_, lean_object* v___x_200_, lean_object* v_staticLib_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lake_buildLeanSharedLibOfStatic___lam__0(v_weakArgs_198_, v_traceArgs_199_, v___x_200_, v_staticLib_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec_ref(v_traceArgs_199_);
lean_dec_ref(v_weakArgs_198_);
return v_res_209_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(lean_object* v_as_210_, size_t v_i_211_, size_t v_stop_212_, uint64_t v_b_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = lean_usize_dec_eq(v_i_211_, v_stop_212_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; size_t v___x_220_; size_t v___x_221_; 
v___x_215_ = lean_array_uget_borrowed(v_as_210_, v_i_211_);
v___x_216_ = l_Lake_Hash_nil;
v___x_217_ = lean_string_hash(v___x_215_);
v___x_218_ = lean_uint64_mix_hash(v___x_216_, v___x_217_);
v___x_219_ = lean_uint64_mix_hash(v_b_213_, v___x_218_);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_add(v_i_211_, v___x_220_);
v_i_211_ = v___x_221_;
v_b_213_ = v___x_219_;
goto _start;
}
else
{
return v_b_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(lean_object* v_as_223_, lean_object* v_i_224_, lean_object* v_stop_225_, lean_object* v_b_226_){
_start:
{
size_t v_i_boxed_227_; size_t v_stop_boxed_228_; uint64_t v_b_boxed_229_; uint64_t v_res_230_; lean_object* v_r_231_; 
v_i_boxed_227_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_stop_boxed_228_ = lean_unbox_usize(v_stop_225_);
lean_dec(v_stop_225_);
v_b_boxed_229_ = lean_unbox_uint64(v_b_226_);
lean_dec_ref(v_b_226_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_as_223_, v_i_boxed_227_, v_stop_boxed_228_, v_b_boxed_229_);
lean_dec_ref(v_as_223_);
v_r_231_ = lean_box_uint64(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
return v_x_233_;
}
else
{
lean_object* v_head_235_; lean_object* v_tail_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_head_235_ = lean_ctor_get(v_x_234_, 0);
v_tail_236_ = lean_ctor_get(v_x_234_, 1);
v___x_237_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0));
v___x_238_ = lean_string_append(v_x_233_, v___x_237_);
v___x_239_ = lean_string_append(v___x_238_, v_head_235_);
v_x_233_ = v___x_239_;
v_x_234_ = v_tail_236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v_x_241_, v_x_242_);
lean_dec(v_x_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_object* v___x_248_; 
v___x_248_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0));
return v___x_248_;
}
else
{
lean_object* v_tail_249_; 
v_tail_249_ = lean_ctor_get(v_x_247_, 1);
if (lean_obj_tag(v_tail_249_) == 0)
{
lean_object* v_head_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_head_250_ = lean_ctor_get(v_x_247_, 0);
v___x_251_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_252_ = lean_string_append(v___x_251_, v_head_250_);
v___x_253_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2));
v___x_254_ = lean_string_append(v___x_252_, v___x_253_);
return v___x_254_;
}
else
{
lean_object* v_head_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint32_t v___x_259_; lean_object* v___x_260_; 
v_head_255_ = lean_ctor_get(v_x_247_, 0);
v___x_256_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_257_ = lean_string_append(v___x_256_, v_head_255_);
v___x_258_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v___x_257_, v_tail_249_);
v___x_259_ = 93;
v___x_260_ = lean_string_push(v___x_258_, v___x_259_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v_x_261_);
lean_dec(v_x_261_);
return v_res_262_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_nat_to_int(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4(void){
_start:
{
uint32_t v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = 0;
v___x_270_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3);
v___x_271_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set_uint32(v___x_271_, sizeof(void*)*1, v___x_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object* v_traceArgs_272_, lean_object* v_weakArgs_273_, lean_object* v_staticLib_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_log_282_; uint8_t v_action_283_; uint8_t v_wantsRebuild_284_; lean_object* v_trace_285_; lean_object* v_buildTime_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_343_; 
v_log_282_ = lean_ctor_get(v___y_280_, 0);
v_action_283_ = lean_ctor_get_uint8(v___y_280_, sizeof(void*)*3);
v_wantsRebuild_284_ = lean_ctor_get_uint8(v___y_280_, sizeof(void*)*3 + 1);
v_trace_285_ = lean_ctor_get(v___y_280_, 1);
v_buildTime_286_ = lean_ctor_get(v___y_280_, 2);
v_isSharedCheck_343_ = !lean_is_exclusive(v___y_280_);
if (v_isSharedCheck_343_ == 0)
{
v___x_288_ = v___y_280_;
v_isShared_289_ = v_isSharedCheck_343_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_buildTime_286_);
lean_inc(v_trace_285_);
lean_inc(v_log_282_);
lean_dec(v___y_280_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_343_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_leanTrace_290_; lean_object* v___x_291_; uint64_t v___y_293_; uint64_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_leanTrace_290_ = lean_ctor_get(v___y_279_, 2);
lean_inc_ref(v_leanTrace_290_);
v___x_291_ = l_Lake_BuildTrace_mix(v_trace_285_, v_leanTrace_290_);
v___x_332_ = l_Lake_Hash_nil;
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_array_get_size(v_traceArgs_272_);
v___x_335_ = lean_nat_dec_lt(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
v___y_293_ = v___x_332_;
goto v___jp_292_;
}
else
{
uint8_t v___x_336_; 
v___x_336_ = lean_nat_dec_le(v___x_334_, v___x_334_);
if (v___x_336_ == 0)
{
if (v___x_335_ == 0)
{
v___y_293_ = v___x_332_;
goto v___jp_292_;
}
else
{
size_t v___x_337_; size_t v___x_338_; uint64_t v___x_339_; 
v___x_337_ = ((size_t)0ULL);
v___x_338_ = lean_usize_of_nat(v___x_334_);
v___x_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_272_, v___x_337_, v___x_338_, v___x_332_);
v___y_293_ = v___x_339_;
goto v___jp_292_;
}
}
else
{
size_t v___x_340_; size_t v___x_341_; uint64_t v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_334_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_272_, v___x_340_, v___x_341_, v___x_332_);
v___y_293_ = v___x_342_;
goto v___jp_292_;
}
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_294_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0));
v___x_295_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1));
lean_inc_ref(v_traceArgs_272_);
v___x_296_ = lean_array_to_list(v_traceArgs_272_);
v___x_297_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v___x_296_);
lean_dec(v___x_296_);
v___x_298_ = lean_string_append(v___x_295_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_299_ = lean_string_append(v___x_294_, v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2));
v___x_301_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4);
v___x_302_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_302_, 0, v___x_299_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
lean_ctor_set_uint64(v___x_302_, sizeof(void*)*3, v___y_293_);
v___x_303_ = l_Lake_BuildTrace_mix(v___x_291_, v___x_302_);
v___x_304_ = l_Lake_platformTrace;
v___x_305_ = l_Lake_BuildTrace_mix(v___x_303_, v___x_304_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_305_);
v___x_307_ = v___x_288_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_log_282_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_buildTime_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*3, v_action_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*3 + 1, v_wantsRebuild_284_);
v___x_307_ = v_reuseFailAlloc_331_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___f_310_; uint8_t v___x_311_; lean_object* v___x_312_; 
v___x_308_ = l_Lake_sharedLibExt;
lean_inc_ref(v_staticLib_274_);
v___x_309_ = l_System_FilePath_withExtension(v_staticLib_274_, v___x_308_);
lean_inc_ref_n(v___x_309_, 2);
v___f_310_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed), 11, 4);
lean_closure_set(v___f_310_, 0, v_weakArgs_273_);
lean_closure_set(v___f_310_, 1, v_traceArgs_272_);
lean_closure_set(v___f_310_, 2, v___x_309_);
lean_closure_set(v___f_310_, 3, v_staticLib_274_);
v___x_311_ = 0;
v___x_312_ = l_Lake_buildFileUnlessUpToDate_x27(v___x_309_, v___f_310_, v___x_311_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___x_307_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_a_313_ = lean_ctor_get(v___x_312_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_312_, 0);
lean_dec(v_unused_321_);
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_309_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec_ref(v___x_309_);
v_a_322_ = lean_ctor_get(v___x_312_, 0);
v_a_323_ = lean_ctor_get(v___x_312_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_312_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_inc(v_a_322_);
lean_dec(v___x_312_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object* v_traceArgs_344_, lean_object* v_weakArgs_345_, lean_object* v_staticLib_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lake_buildLeanSharedLibOfStatic___lam__1(v_traceArgs_344_, v_weakArgs_345_, v_staticLib_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec(v___y_349_);
lean_dec(v___y_348_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* v_staticLibJob_355_, lean_object* v_weakArgs_356_, lean_object* v_traceArgs_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; 
v___f_365_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed), 10, 2);
lean_closure_set(v___f_365_, 0, v_traceArgs_357_);
lean_closure_set(v___f_365_, 1, v_weakArgs_356_);
v___x_366_ = l_Lake_instDataKindFilePath;
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = 0;
v___x_369_ = l_Lake_Job_mapM___redArg(v___x_366_, v_staticLibJob_355_, v___f_365_, v___x_367_, v___x_368_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object* v_staticLibJob_370_, lean_object* v_weakArgs_371_, lean_object* v_traceArgs_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lake_buildLeanSharedLibOfStatic(v_staticLibJob_370_, v_weakArgs_371_, v_traceArgs_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
lean_dec_ref(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec(v_a_375_);
lean_dec(v_a_374_);
return v_res_380_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1));
v___x_385_ = l_Lake_BuildTrace_nil(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object* v___x_386_, lean_object* v_config_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
lean_inc_ref(v___y_388_);
lean_inc_ref(v___y_392_);
lean_inc(v___y_391_);
lean_inc(v___y_390_);
lean_inc(v___y_389_);
v___x_395_ = lean_apply_7(v___y_388_, v___x_386_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, lean_box(0));
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_toLeanConfig_396_; lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_409_; 
v_toLeanConfig_396_ = lean_ctor_get(v_config_387_, 1);
lean_inc_ref(v_toLeanConfig_396_);
lean_dec_ref(v_config_387_);
v_a_397_ = lean_ctor_get(v___x_395_, 0);
v_a_398_ = lean_ctor_get(v___x_395_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_409_ == 0)
{
v___x_400_ = v___x_395_;
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_inc(v_a_397_);
lean_dec(v___x_395_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_moreLinkArgs_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v_moreLinkArgs_402_ = lean_ctor_get(v_toLeanConfig_396_, 8);
lean_inc_ref(v_moreLinkArgs_402_);
lean_dec_ref(v_toLeanConfig_396_);
v___x_403_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0));
v___x_404_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_405_ = l_Lake_buildLeanSharedLibOfStatic(v_a_397_, v_moreLinkArgs_402_, v___x_403_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___x_404_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_405_);
v___x_407_ = v___x_400_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_a_398_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_dec_ref(v___y_388_);
lean_dec_ref(v_config_387_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object* v___x_410_, lean_object* v_config_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(v___x_410_, v_config_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec(v___y_414_);
lean_dec(v___y_413_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object* v_lib_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_pkg_429_; lean_object* v_name_430_; lean_object* v_keyName_431_; lean_object* v_config_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___f_438_; lean_object* v___x_439_; 
v_pkg_429_ = lean_ctor_get(v_lib_421_, 0);
v_name_430_ = lean_ctor_get(v_lib_421_, 1);
lean_inc_n(v_name_430_, 2);
v_keyName_431_ = lean_ctor_get(v_pkg_429_, 2);
v_config_432_ = lean_ctor_get(v_pkg_429_, 6);
lean_inc_ref(v_config_432_);
v___x_433_ = l_Lake_instDataKindFilePath;
v___x_434_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_keyName_431_);
v___x_435_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_435_, 0, v_keyName_431_);
lean_ctor_set(v___x_435_, 1, v_name_430_);
v___x_436_ = l_Lake_ExternLib_keyword;
v___x_437_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
lean_ctor_set(v___x_437_, 2, v_lib_421_);
lean_ctor_set(v___x_437_, 3, v___x_434_);
v___f_438_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed), 9, 2);
lean_closure_set(v___f_438_, 0, v___x_437_);
lean_closure_set(v___f_438_, 1, v_config_432_);
v___x_439_ = l_Lake_ensureJob___redArg(v___x_433_, v___f_438_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_471_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_a_441_ = lean_ctor_get(v___x_439_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_471_ == 0)
{
v___x_443_ = v___x_439_;
v_isShared_444_ = v_isSharedCheck_471_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_471_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_task_445_; lean_object* v_kind_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_469_; 
v_task_445_ = lean_ctor_get(v_a_440_, 0);
v_kind_446_ = lean_ctor_get(v_a_440_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_440_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_a_440_, 2);
lean_dec(v_unused_470_);
v___x_448_ = v_a_440_;
v_isShared_449_ = v_isSharedCheck_469_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_kind_446_);
lean_inc(v_task_445_);
lean_dec(v_a_440_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_469_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_registeredJobs_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v_job_460_; 
v_registeredJobs_450_ = lean_ctor_get(v_a_426_, 3);
v___x_451_ = lean_st_ref_take(v_registeredJobs_450_);
v___x_452_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_453_ = l_Lean_Name_str___override(v_name_430_, v___x_452_);
v___x_454_ = 1;
v___x_455_ = l_Lean_Name_toString(v___x_453_, v___x_454_);
v___x_456_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0));
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
v___x_458_ = 0;
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 2, v___x_457_);
v_job_460_ = v___x_448_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_task_445_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_kind_446_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v___x_457_);
v_job_460_ = v_reuseFailAlloc_468_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
lean_ctor_set_uint8(v_job_460_, sizeof(void*)*3, v___x_458_);
lean_inc_ref(v_job_460_);
v___x_461_ = l_Lake_Job_toOpaque___redArg(v_job_460_);
v___x_462_ = lean_array_push(v___x_451_, v___x_461_);
v___x_463_ = lean_st_ref_set(v_registeredJobs_450_, v___x_462_);
v___x_464_ = l_Lake_Job_renew___redArg(v_job_460_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_464_);
v___x_466_ = v___x_443_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_a_441_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
else
{
lean_dec(v_name_430_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object* v_lib_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(v_lib_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec(v_a_475_);
lean_dec(v_a_474_);
return v_res_480_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___f_482_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_483_ = 1;
v___x_484_ = l_Lake_instDataKindFilePath;
v___x_485_ = ((lean_object*)(l_Lake_ExternLib_sharedFacetConfig___closed__0));
v___x_486_ = l_Lake_ExternLib_keyword;
v___x_487_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
lean_ctor_set(v___x_487_, 3, v___f_482_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*4, v___x_483_);
lean_ctor_set_uint8(v___x_487_, sizeof(void*)*4 + 1, v___x_483_);
return v___x_487_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Lake_ExternLib_sharedFacetConfig___closed__1, &l_Lake_ExternLib_sharedFacetConfig___closed__1_once, _init_l_Lake_ExternLib_sharedFacetConfig___closed__1);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3));
v___x_495_ = lean_string_utf8_byte_size(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object* v_sharedLib_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
lean_inc_ref(v_sharedLib_497_);
v___x_505_ = l_System_FilePath_fileStem(v_sharedLib_497_);
if (lean_obj_tag(v___x_505_) == 1)
{
lean_object* v_val_506_; uint8_t v___x_507_; uint8_t v___y_509_; 
v_val_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = l_System_Platform_isWindows;
if (v___x_507_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_540_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3));
v___x_541_ = lean_string_utf8_byte_size(v_val_506_);
v___x_542_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4, &l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_once, _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4);
v___x_543_ = lean_nat_dec_le(v___x_542_, v___x_541_);
if (v___x_543_ == 0)
{
v___y_509_ = v___x_507_;
goto v___jp_508_;
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_string_memcmp(v_val_506_, v___x_540_, v___x_544_, v___x_544_, v___x_542_);
v___y_509_ = v___x_545_;
goto v___jp_508_;
}
}
else
{
uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = 0;
v___x_547_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_548_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_548_, 0, v_sharedLib_497_);
lean_ctor_set(v___x_548_, 1, v_val_506_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
lean_ctor_set(v___x_548_, 3, v___x_547_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*4, v___x_546_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___y_503_);
return v___x_549_;
}
v___jp_508_:
{
if (v___y_509_ == 0)
{
lean_object* v_log_510_; uint8_t v_action_511_; uint8_t v_wantsRebuild_512_; lean_object* v_trace_513_; lean_object* v_buildTime_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_530_; 
lean_dec(v_val_506_);
v_log_510_ = lean_ctor_get(v___y_503_, 0);
v_action_511_ = lean_ctor_get_uint8(v___y_503_, sizeof(void*)*3);
v_wantsRebuild_512_ = lean_ctor_get_uint8(v___y_503_, sizeof(void*)*3 + 1);
v_trace_513_ = lean_ctor_get(v___y_503_, 1);
v_buildTime_514_ = lean_ctor_get(v___y_503_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v___y_503_);
if (v_isSharedCheck_530_ == 0)
{
v___x_516_ = v___y_503_;
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_buildTime_514_);
lean_inc(v_trace_513_);
lean_inc(v_log_510_);
lean_dec(v___y_503_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_530_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_518_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_519_ = lean_string_append(v___x_518_, v_sharedLib_497_);
lean_dec_ref(v_sharedLib_497_);
v___x_520_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1));
v___x_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = 3;
v___x_523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*1, v___x_522_);
v___x_524_ = lean_array_get_size(v_log_510_);
v___x_525_ = lean_array_push(v_log_510_, v___x_523_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_525_);
v___x_527_ = v___x_516_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_trace_513_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_buildTime_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3, v_action_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3 + 1, v_wantsRebuild_512_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_524_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_531_ = lean_unsigned_to_nat(3u);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_string_utf8_byte_size(v_val_506_);
lean_inc(v_val_506_);
v___x_534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_534_, 0, v_val_506_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_533_);
v___x_535_ = l_String_Slice_Pos_nextn(v___x_534_, v___x_532_, v___x_531_);
lean_dec_ref_known(v___x_534_, 3);
v___x_536_ = lean_string_utf8_extract_fast(v_val_506_, v___x_535_, v___x_533_);
lean_dec(v___x_535_);
lean_dec(v_val_506_);
v___x_537_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_538_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_538_, 0, v_sharedLib_497_);
lean_ctor_set(v___x_538_, 1, v___x_536_);
lean_ctor_set(v___x_538_, 2, v___x_537_);
lean_ctor_set(v___x_538_, 3, v___x_537_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*4, v___x_507_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___y_503_);
return v___x_539_;
}
}
}
else
{
lean_object* v_log_550_; uint8_t v_action_551_; uint8_t v_wantsRebuild_552_; lean_object* v_trace_553_; lean_object* v_buildTime_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_570_; 
lean_dec(v___x_505_);
v_log_550_ = lean_ctor_get(v___y_503_, 0);
v_action_551_ = lean_ctor_get_uint8(v___y_503_, sizeof(void*)*3);
v_wantsRebuild_552_ = lean_ctor_get_uint8(v___y_503_, sizeof(void*)*3 + 1);
v_trace_553_ = lean_ctor_get(v___y_503_, 1);
v_buildTime_554_ = lean_ctor_get(v___y_503_, 2);
v_isSharedCheck_570_ = !lean_is_exclusive(v___y_503_);
if (v_isSharedCheck_570_ == 0)
{
v___x_556_ = v___y_503_;
v_isShared_557_ = v_isSharedCheck_570_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_buildTime_554_);
lean_inc(v_trace_553_);
lean_inc(v_log_550_);
lean_dec(v___y_503_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_570_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_558_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_559_ = lean_string_append(v___x_558_, v_sharedLib_497_);
lean_dec_ref(v_sharedLib_497_);
v___x_560_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5));
v___x_561_ = lean_string_append(v___x_559_, v___x_560_);
v___x_562_ = 3;
v___x_563_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*1, v___x_562_);
v___x_564_ = lean_array_get_size(v_log_550_);
v___x_565_ = lean_array_push(v_log_550_, v___x_563_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_565_);
v___x_567_ = v___x_556_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_trace_553_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_buildTime_554_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3, v_action_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3 + 1, v_wantsRebuild_552_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_564_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object* v_sharedLib_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(v_sharedLib_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object* v_sharedLibTarget_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; 
v___f_589_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0));
v___x_590_ = l_Lake_instDataKindDynlib;
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = 0;
v___x_593_ = l_Lake_Job_mapM___redArg(v___x_590_, v_sharedLibTarget_581_, v___f_589_, v___x_591_, v___x_592_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object* v_sharedLibTarget_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_sharedLibTarget_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_a_598_);
lean_dec(v_a_597_);
lean_dec(v_a_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object* v___x_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; 
lean_inc_ref(v___y_604_);
lean_inc_ref(v___y_608_);
lean_inc(v___y_607_);
lean_inc(v___y_606_);
lean_inc(v___y_605_);
v___x_611_ = lean_apply_7(v___y_604_, v___x_603_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, lean_box(0));
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_622_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_a_613_ = lean_ctor_get(v___x_611_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_622_ == 0)
{
v___x_615_ = v___x_611_;
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_618_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_a_612_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___x_617_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_618_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_a_613_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v___y_604_);
v_a_623_ = lean_ctor_get(v___x_611_, 0);
v_a_624_ = lean_ctor_get(v___x_611_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_611_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_inc(v_a_623_);
lean_dec(v___x_611_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_623_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object* v___x_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(v___x_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
lean_dec(v___y_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object* v_lib_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_pkg_650_; lean_object* v_name_651_; lean_object* v_keyName_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___f_658_; lean_object* v___x_659_; 
v_pkg_650_ = lean_ctor_get(v_lib_642_, 0);
v_name_651_ = lean_ctor_get(v_lib_642_, 1);
lean_inc_n(v_name_651_, 2);
v_keyName_652_ = lean_ctor_get(v_pkg_650_, 2);
v___x_653_ = l_Lake_instDataKindDynlib;
v___x_654_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_keyName_652_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v_keyName_652_);
lean_ctor_set(v___x_655_, 1, v_name_651_);
v___x_656_ = l_Lake_ExternLib_keyword;
v___x_657_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
lean_ctor_set(v___x_657_, 2, v_lib_642_);
lean_ctor_set(v___x_657_, 3, v___x_654_);
v___f_658_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed), 8, 1);
lean_closure_set(v___f_658_, 0, v___x_657_);
v___x_659_ = l_Lake_ensureJob___redArg(v___x_653_, v___f_658_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_691_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_a_661_ = lean_ctor_get(v___x_659_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_691_ == 0)
{
v___x_663_ = v___x_659_;
v_isShared_664_ = v_isSharedCheck_691_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_691_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_task_665_; lean_object* v_kind_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_689_; 
v_task_665_ = lean_ctor_get(v_a_660_, 0);
v_kind_666_ = lean_ctor_get(v_a_660_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_a_660_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v_a_660_, 2);
lean_dec(v_unused_690_);
v___x_668_ = v_a_660_;
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_kind_666_);
lean_inc(v_task_665_);
lean_dec(v_a_660_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_689_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_registeredJobs_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; lean_object* v_job_680_; 
v_registeredJobs_670_ = lean_ctor_get(v_a_647_, 3);
v___x_671_ = lean_st_ref_take(v_registeredJobs_670_);
v___x_672_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_673_ = l_Lean_Name_str___override(v_name_651_, v___x_672_);
v___x_674_ = 1;
v___x_675_ = l_Lean_Name_toString(v___x_673_, v___x_674_);
v___x_676_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0));
v___x_677_ = lean_string_append(v___x_675_, v___x_676_);
v___x_678_ = 0;
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 2, v___x_677_);
v_job_680_ = v___x_668_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_task_665_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_kind_666_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v___x_677_);
v_job_680_ = v_reuseFailAlloc_688_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
lean_ctor_set_uint8(v_job_680_, sizeof(void*)*3, v___x_678_);
lean_inc_ref(v_job_680_);
v___x_681_ = l_Lake_Job_toOpaque___redArg(v_job_680_);
v___x_682_ = lean_array_push(v___x_671_, v___x_681_);
v___x_683_ = lean_st_ref_set(v_registeredJobs_670_, v___x_682_);
v___x_684_ = l_Lake_Job_renew___redArg(v_job_680_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_684_);
v___x_686_ = v___x_663_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_661_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
else
{
lean_dec(v_name_651_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object* v_lib_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(v_lib_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec(v_a_695_);
lean_dec(v_a_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t v_fmt_701_, lean_object* v_a_702_){
_start:
{
if (v_fmt_701_ == 0)
{
lean_object* v_path_703_; 
v_path_703_ = lean_ctor_get(v_a_702_, 0);
lean_inc_ref(v_path_703_);
return v_path_703_;
}
else
{
lean_object* v_path_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_path_704_ = lean_ctor_get(v_a_702_, 0);
lean_inc_ref(v_path_704_);
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v_path_704_);
v___x_706_ = l_Lean_Json_compress(v___x_705_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object* v_fmt_707_, lean_object* v_a_708_){
_start:
{
uint8_t v_fmt_boxed_709_; lean_object* v_res_710_; 
v_fmt_boxed_709_ = lean_unbox(v_fmt_707_);
v_res_710_ = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(v_fmt_boxed_709_, v_a_708_);
lean_dec_ref(v_a_708_);
return v_res_710_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___f_713_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__0));
v___x_714_ = 1;
v___x_715_ = l_Lake_instDataKindDynlib;
v___x_716_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__1));
v___x_717_ = l_Lake_ExternLib_keyword;
v___x_718_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_715_);
lean_ctor_set(v___x_718_, 3, v___f_713_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*4, v___x_714_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*4 + 1, v___x_714_);
return v___x_718_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig(void){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_Lake_ExternLib_dynlibFacetConfig___closed__2, &l_Lake_ExternLib_dynlibFacetConfig___closed__2_once, _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object* v_lib_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_pkg_728_; lean_object* v_name_729_; lean_object* v_keyName_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_pkg_728_ = lean_ctor_get(v_lib_720_, 0);
v_name_729_ = lean_ctor_get(v_lib_720_, 1);
v_keyName_730_ = lean_ctor_get(v_pkg_728_, 2);
v___x_731_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_729_);
lean_inc(v_keyName_730_);
v___x_732_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_732_, 0, v_keyName_730_);
lean_ctor_set(v___x_732_, 1, v_name_729_);
v___x_733_ = l_Lake_ExternLib_keyword;
v___x_734_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
lean_ctor_set(v___x_734_, 2, v_lib_720_);
lean_ctor_set(v___x_734_, 3, v___x_731_);
lean_inc_ref(v_a_725_);
lean_inc(v_a_724_);
lean_inc(v_a_723_);
lean_inc(v_a_722_);
v___x_735_ = lean_apply_7(v_a_721_, v___x_734_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, lean_box(0));
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object* v_lib_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(v_lib_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec(v_a_739_);
lean_dec(v_a_738_);
return v_res_744_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_746_; lean_object* v___f_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_746_ = 0;
v___f_747_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_748_ = 1;
v___x_749_ = l_Lake_instDataKindFilePath;
v___x_750_ = ((lean_object*)(l_Lake_ExternLib_defaultFacetConfig___closed__0));
v___x_751_ = l_Lake_ExternLib_keyword;
v___x_752_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
lean_ctor_set(v___x_752_, 2, v___x_749_);
lean_ctor_set(v___x_752_, 3, v___f_747_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*4, v___x_748_);
lean_ctor_set_uint8(v___x_752_, sizeof(void*)*4 + 1, v___x_746_);
return v___x_752_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_obj_once(&l_Lake_ExternLib_defaultFacetConfig___closed__1, &l_Lake_ExternLib_defaultFacetConfig___closed__1_once, _init_l_Lake_ExternLib_defaultFacetConfig___closed__1);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_754_, lean_object* v_v_755_, lean_object* v_t_756_){
_start:
{
if (lean_obj_tag(v_t_756_) == 0)
{
lean_object* v_size_757_; lean_object* v_k_758_; lean_object* v_v_759_; lean_object* v_l_760_; lean_object* v_r_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_1041_; 
v_size_757_ = lean_ctor_get(v_t_756_, 0);
v_k_758_ = lean_ctor_get(v_t_756_, 1);
v_v_759_ = lean_ctor_get(v_t_756_, 2);
v_l_760_ = lean_ctor_get(v_t_756_, 3);
v_r_761_ = lean_ctor_get(v_t_756_, 4);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_t_756_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_763_ = v_t_756_;
v_isShared_764_ = v_isSharedCheck_1041_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_r_761_);
lean_inc(v_l_760_);
lean_inc(v_v_759_);
lean_inc(v_k_758_);
lean_inc(v_size_757_);
lean_dec(v_t_756_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_1041_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___x_765_; 
v___x_765_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_754_, v_k_758_);
switch(v___x_765_)
{
case 0:
{
lean_object* v_impl_766_; lean_object* v___x_767_; 
lean_dec(v_size_757_);
v_impl_766_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_754_, v_v_755_, v_l_760_);
v___x_767_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_761_) == 0)
{
lean_object* v_size_768_; lean_object* v_size_769_; lean_object* v_k_770_; lean_object* v_v_771_; lean_object* v_l_772_; lean_object* v_r_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_size_768_ = lean_ctor_get(v_r_761_, 0);
v_size_769_ = lean_ctor_get(v_impl_766_, 0);
lean_inc(v_size_769_);
v_k_770_ = lean_ctor_get(v_impl_766_, 1);
lean_inc(v_k_770_);
v_v_771_ = lean_ctor_get(v_impl_766_, 2);
lean_inc(v_v_771_);
v_l_772_ = lean_ctor_get(v_impl_766_, 3);
lean_inc(v_l_772_);
v_r_773_ = lean_ctor_get(v_impl_766_, 4);
lean_inc(v_r_773_);
v___x_774_ = lean_unsigned_to_nat(3u);
v___x_775_ = lean_nat_mul(v___x_774_, v_size_768_);
v___x_776_ = lean_nat_dec_lt(v___x_775_, v_size_769_);
lean_dec(v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec(v_r_773_);
lean_dec(v_l_772_);
lean_dec(v_v_771_);
lean_dec(v_k_770_);
v___x_777_ = lean_nat_add(v___x_767_, v_size_769_);
lean_dec(v_size_769_);
v___x_778_ = lean_nat_add(v___x_777_, v_size_768_);
lean_dec(v___x_777_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 3, v_impl_766_);
lean_ctor_set(v___x_763_, 0, v___x_778_);
v___x_780_ = v___x_763_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_impl_766_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_r_761_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
else
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_847_; 
v_isSharedCheck_847_ = !lean_is_exclusive(v_impl_766_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; lean_object* v_unused_851_; lean_object* v_unused_852_; 
v_unused_848_ = lean_ctor_get(v_impl_766_, 4);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_impl_766_, 3);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_impl_766_, 2);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_impl_766_, 1);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_impl_766_, 0);
lean_dec(v_unused_852_);
v___x_783_ = v_impl_766_;
v_isShared_784_ = v_isSharedCheck_847_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_impl_766_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_847_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_size_785_; lean_object* v_size_786_; lean_object* v_k_787_; lean_object* v_v_788_; lean_object* v_l_789_; lean_object* v_r_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_size_785_ = lean_ctor_get(v_l_772_, 0);
v_size_786_ = lean_ctor_get(v_r_773_, 0);
v_k_787_ = lean_ctor_get(v_r_773_, 1);
v_v_788_ = lean_ctor_get(v_r_773_, 2);
v_l_789_ = lean_ctor_get(v_r_773_, 3);
v_r_790_ = lean_ctor_get(v_r_773_, 4);
v___x_791_ = lean_unsigned_to_nat(2u);
v___x_792_ = lean_nat_mul(v___x_791_, v_size_785_);
v___x_793_ = lean_nat_dec_lt(v_size_786_, v___x_792_);
lean_dec(v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_822_; 
lean_inc(v_r_790_);
lean_inc(v_l_789_);
lean_inc(v_v_788_);
lean_inc(v_k_787_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_r_773_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; lean_object* v_unused_827_; 
v_unused_823_ = lean_ctor_get(v_r_773_, 4);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_r_773_, 3);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_r_773_, 2);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_r_773_, 1);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_r_773_, 0);
lean_dec(v_unused_827_);
v___x_795_ = v_r_773_;
v_isShared_796_ = v_isSharedCheck_822_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_r_773_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_822_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___x_810_; lean_object* v___y_812_; 
v___x_797_ = lean_nat_add(v___x_767_, v_size_769_);
lean_dec(v_size_769_);
v___x_798_ = lean_nat_add(v___x_797_, v_size_768_);
lean_dec(v___x_797_);
v___x_810_ = lean_nat_add(v___x_767_, v_size_785_);
if (lean_obj_tag(v_l_789_) == 0)
{
lean_object* v_size_820_; 
v_size_820_ = lean_ctor_get(v_l_789_, 0);
lean_inc(v_size_820_);
v___y_812_ = v_size_820_;
goto v___jp_811_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = lean_unsigned_to_nat(0u);
v___y_812_ = v___x_821_;
goto v___jp_811_;
}
v___jp_799_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_nat_add(v___y_800_, v___y_802_);
lean_dec(v___y_802_);
lean_dec(v___y_800_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 4, v_r_761_);
lean_ctor_set(v___x_795_, 3, v_r_790_);
lean_ctor_set(v___x_795_, 2, v_v_759_);
lean_ctor_set(v___x_795_, 1, v_k_758_);
lean_ctor_set(v___x_795_, 0, v___x_803_);
v___x_805_ = v___x_795_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v_r_790_);
lean_ctor_set(v_reuseFailAlloc_809_, 4, v_r_761_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 4, v___x_805_);
lean_ctor_set(v___x_783_, 3, v___y_801_);
lean_ctor_set(v___x_783_, 2, v_v_788_);
lean_ctor_set(v___x_783_, 1, v_k_787_);
lean_ctor_set(v___x_783_, 0, v___x_798_);
v___x_807_ = v___x_783_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_787_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_788_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v___y_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_nat_add(v___x_810_, v___y_812_);
lean_dec(v___y_812_);
lean_dec(v___x_810_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_l_789_);
lean_ctor_set(v___x_763_, 3, v_l_772_);
lean_ctor_set(v___x_763_, 2, v_v_771_);
lean_ctor_set(v___x_763_, 1, v_k_770_);
lean_ctor_set(v___x_763_, 0, v___x_813_);
v___x_815_ = v___x_763_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_l_772_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_l_789_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; 
v___x_816_ = lean_nat_add(v___x_767_, v_size_768_);
if (lean_obj_tag(v_r_790_) == 0)
{
lean_object* v_size_817_; 
v_size_817_ = lean_ctor_get(v_r_790_, 0);
lean_inc(v_size_817_);
v___y_800_ = v___x_816_;
v___y_801_ = v___x_815_;
v___y_802_ = v_size_817_;
goto v___jp_799_;
}
else
{
lean_object* v___x_818_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v___y_800_ = v___x_816_;
v___y_801_ = v___x_815_;
v___y_802_ = v___x_818_;
goto v___jp_799_;
}
}
}
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
lean_del_object(v___x_763_);
v___x_828_ = lean_nat_add(v___x_767_, v_size_769_);
lean_dec(v_size_769_);
v___x_829_ = lean_nat_add(v___x_828_, v_size_768_);
lean_dec(v___x_828_);
v___x_830_ = lean_nat_add(v___x_767_, v_size_768_);
v___x_831_ = lean_nat_add(v___x_830_, v_size_786_);
lean_dec(v___x_830_);
lean_inc_ref(v_r_761_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 4, v_r_761_);
lean_ctor_set(v___x_783_, 3, v_r_773_);
lean_ctor_set(v___x_783_, 2, v_v_759_);
lean_ctor_set(v___x_783_, 1, v_k_758_);
lean_ctor_set(v___x_783_, 0, v___x_831_);
v___x_833_ = v___x_783_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_r_773_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_r_761_);
v___x_833_ = v_reuseFailAlloc_846_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_isSharedCheck_840_ = !lean_is_exclusive(v_r_761_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_841_ = lean_ctor_get(v_r_761_, 4);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_r_761_, 3);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_r_761_, 2);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_r_761_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_r_761_, 0);
lean_dec(v_unused_845_);
v___x_835_ = v_r_761_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_r_761_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 4, v___x_833_);
lean_ctor_set(v___x_835_, 3, v_l_772_);
lean_ctor_set(v___x_835_, 2, v_v_771_);
lean_ctor_set(v___x_835_, 1, v_k_770_);
lean_ctor_set(v___x_835_, 0, v___x_829_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_k_770_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_v_771_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_l_772_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v___x_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_853_; 
v_l_853_ = lean_ctor_get(v_impl_766_, 3);
lean_inc(v_l_853_);
if (lean_obj_tag(v_l_853_) == 0)
{
lean_object* v_r_854_; lean_object* v_k_855_; lean_object* v_v_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_867_; 
v_r_854_ = lean_ctor_get(v_impl_766_, 4);
v_k_855_ = lean_ctor_get(v_impl_766_, 1);
v_v_856_ = lean_ctor_get(v_impl_766_, 2);
v_isSharedCheck_867_ = !lean_is_exclusive(v_impl_766_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_868_ = lean_ctor_get(v_impl_766_, 3);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_impl_766_, 0);
lean_dec(v_unused_869_);
v___x_858_ = v_impl_766_;
v_isShared_859_ = v_isSharedCheck_867_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_r_854_);
lean_inc(v_v_856_);
lean_inc(v_k_855_);
lean_dec(v_impl_766_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_867_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_854_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 3, v_r_854_);
lean_ctor_set(v___x_858_, 2, v_v_759_);
lean_ctor_set(v___x_858_, 1, v_k_758_);
lean_ctor_set(v___x_858_, 0, v___x_767_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_r_854_);
lean_ctor_set(v_reuseFailAlloc_866_, 4, v_r_854_);
v___x_862_ = v_reuseFailAlloc_866_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v___x_862_);
lean_ctor_set(v___x_763_, 3, v_l_853_);
lean_ctor_set(v___x_763_, 2, v_v_856_);
lean_ctor_set(v___x_763_, 1, v_k_855_);
lean_ctor_set(v___x_763_, 0, v___x_860_);
v___x_864_ = v___x_763_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_l_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_object* v_r_870_; 
v_r_870_ = lean_ctor_get(v_impl_766_, 4);
lean_inc(v_r_870_);
if (lean_obj_tag(v_r_870_) == 0)
{
lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_895_; 
v_k_871_ = lean_ctor_get(v_impl_766_, 1);
v_v_872_ = lean_ctor_get(v_impl_766_, 2);
v_isSharedCheck_895_ = !lean_is_exclusive(v_impl_766_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; lean_object* v_unused_897_; lean_object* v_unused_898_; 
v_unused_896_ = lean_ctor_get(v_impl_766_, 4);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_impl_766_, 3);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_impl_766_, 0);
lean_dec(v_unused_898_);
v___x_874_ = v_impl_766_;
v_isShared_875_ = v_isSharedCheck_895_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_v_872_);
lean_inc(v_k_871_);
lean_dec(v_impl_766_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_895_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_k_876_; lean_object* v_v_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_891_; 
v_k_876_ = lean_ctor_get(v_r_870_, 1);
v_v_877_ = lean_ctor_get(v_r_870_, 2);
v_isSharedCheck_891_ = !lean_is_exclusive(v_r_870_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_892_ = lean_ctor_get(v_r_870_, 4);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_r_870_, 3);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_r_870_, 0);
lean_dec(v_unused_894_);
v___x_879_ = v_r_870_;
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_v_877_);
lean_inc(v_k_876_);
lean_dec(v_r_870_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_891_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_unsigned_to_nat(3u);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 4, v_l_853_);
lean_ctor_set(v___x_879_, 3, v_l_853_);
lean_ctor_set(v___x_879_, 2, v_v_872_);
lean_ctor_set(v___x_879_, 1, v_k_871_);
lean_ctor_set(v___x_879_, 0, v___x_767_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_890_, 3, v_l_853_);
lean_ctor_set(v_reuseFailAlloc_890_, 4, v_l_853_);
v___x_883_ = v_reuseFailAlloc_890_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 4, v_l_853_);
lean_ctor_set(v___x_874_, 2, v_v_759_);
lean_ctor_set(v___x_874_, 1, v_k_758_);
lean_ctor_set(v___x_874_, 0, v___x_767_);
v___x_885_ = v___x_874_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_l_853_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_l_853_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v___x_885_);
lean_ctor_set(v___x_763_, 3, v___x_883_);
lean_ctor_set(v___x_763_, 2, v_v_877_);
lean_ctor_set(v___x_763_, 1, v_k_876_);
lean_ctor_set(v___x_763_, 0, v___x_881_);
v___x_887_ = v___x_763_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_876_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
}
else
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_unsigned_to_nat(2u);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_r_870_);
lean_ctor_set(v___x_763_, 3, v_impl_766_);
lean_ctor_set(v___x_763_, 0, v___x_899_);
v___x_901_ = v___x_763_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_impl_766_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_r_870_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
case 1:
{
lean_object* v___x_904_; 
lean_dec(v_v_759_);
lean_dec(v_k_758_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v_v_755_);
lean_ctor_set(v___x_763_, 1, v_k_754_);
v___x_904_ = v___x_763_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_size_757_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_754_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_755_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_760_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_r_761_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
default: 
{
lean_object* v_impl_906_; lean_object* v___x_907_; 
lean_dec(v_size_757_);
v_impl_906_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_754_, v_v_755_, v_r_761_);
v___x_907_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_760_) == 0)
{
lean_object* v_size_908_; lean_object* v_size_909_; lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v_l_912_; lean_object* v_r_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_size_908_ = lean_ctor_get(v_l_760_, 0);
v_size_909_ = lean_ctor_get(v_impl_906_, 0);
lean_inc(v_size_909_);
v_k_910_ = lean_ctor_get(v_impl_906_, 1);
lean_inc(v_k_910_);
v_v_911_ = lean_ctor_get(v_impl_906_, 2);
lean_inc(v_v_911_);
v_l_912_ = lean_ctor_get(v_impl_906_, 3);
lean_inc(v_l_912_);
v_r_913_ = lean_ctor_get(v_impl_906_, 4);
lean_inc(v_r_913_);
v___x_914_ = lean_unsigned_to_nat(3u);
v___x_915_ = lean_nat_mul(v___x_914_, v_size_908_);
v___x_916_ = lean_nat_dec_lt(v___x_915_, v_size_909_);
lean_dec(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec(v_r_913_);
lean_dec(v_l_912_);
lean_dec(v_v_911_);
lean_dec(v_k_910_);
v___x_917_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_918_ = lean_nat_add(v___x_917_, v_size_909_);
lean_dec(v_size_909_);
lean_dec(v___x_917_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_impl_906_);
lean_ctor_set(v___x_763_, 0, v___x_918_);
v___x_920_ = v___x_763_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_l_760_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_impl_906_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_985_; 
v_isSharedCheck_985_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; 
v_unused_986_ = lean_ctor_get(v_impl_906_, 4);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_impl_906_, 2);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_impl_906_, 1);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_990_);
v___x_923_ = v_impl_906_;
v_isShared_924_ = v_isSharedCheck_985_;
goto v_resetjp_922_;
}
else
{
lean_dec(v_impl_906_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_985_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_size_925_; lean_object* v_k_926_; lean_object* v_v_927_; lean_object* v_l_928_; lean_object* v_r_929_; lean_object* v_size_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_size_925_ = lean_ctor_get(v_l_912_, 0);
v_k_926_ = lean_ctor_get(v_l_912_, 1);
v_v_927_ = lean_ctor_get(v_l_912_, 2);
v_l_928_ = lean_ctor_get(v_l_912_, 3);
v_r_929_ = lean_ctor_get(v_l_912_, 4);
v_size_930_ = lean_ctor_get(v_r_913_, 0);
v___x_931_ = lean_unsigned_to_nat(2u);
v___x_932_ = lean_nat_mul(v___x_931_, v_size_930_);
v___x_933_ = lean_nat_dec_lt(v_size_925_, v___x_932_);
lean_dec(v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_961_; 
lean_inc(v_r_929_);
lean_inc(v_l_928_);
lean_inc(v_v_927_);
lean_inc(v_k_926_);
v_isSharedCheck_961_ = !lean_is_exclusive(v_l_912_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; lean_object* v_unused_966_; 
v_unused_962_ = lean_ctor_get(v_l_912_, 4);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_912_, 3);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_l_912_, 2);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_l_912_, 1);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_l_912_, 0);
lean_dec(v_unused_966_);
v___x_935_ = v_l_912_;
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_l_912_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_951_; 
v___x_937_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_938_ = lean_nat_add(v___x_937_, v_size_909_);
lean_dec(v_size_909_);
if (lean_obj_tag(v_l_928_) == 0)
{
lean_object* v_size_959_; 
v_size_959_ = lean_ctor_get(v_l_928_, 0);
lean_inc(v_size_959_);
v___y_951_ = v_size_959_;
goto v___jp_950_;
}
else
{
lean_object* v___x_960_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___y_951_ = v___x_960_;
goto v___jp_950_;
}
v___jp_939_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_nat_add(v___y_940_, v___y_942_);
lean_dec(v___y_942_);
lean_dec(v___y_940_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v_r_913_);
lean_ctor_set(v___x_935_, 3, v_r_929_);
lean_ctor_set(v___x_935_, 2, v_v_911_);
lean_ctor_set(v___x_935_, 1, v_k_910_);
lean_ctor_set(v___x_935_, 0, v___x_943_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_r_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_r_913_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v___x_945_);
lean_ctor_set(v___x_923_, 3, v___y_941_);
lean_ctor_set(v___x_923_, 2, v_v_927_);
lean_ctor_set(v___x_923_, 1, v_k_926_);
lean_ctor_set(v___x_923_, 0, v___x_938_);
v___x_947_ = v___x_923_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v___y_941_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
v___jp_950_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_nat_add(v___x_937_, v___y_951_);
lean_dec(v___y_951_);
lean_dec(v___x_937_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_l_928_);
lean_ctor_set(v___x_763_, 0, v___x_952_);
v___x_954_ = v___x_763_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_760_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_l_928_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; 
v___x_955_ = lean_nat_add(v___x_907_, v_size_930_);
if (lean_obj_tag(v_r_929_) == 0)
{
lean_object* v_size_956_; 
v_size_956_ = lean_ctor_get(v_r_929_, 0);
lean_inc(v_size_956_);
v___y_940_ = v___x_955_;
v___y_941_ = v___x_954_;
v___y_942_ = v_size_956_;
goto v___jp_939_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___y_940_ = v___x_955_;
v___y_941_ = v___x_954_;
v___y_942_ = v___x_957_;
goto v___jp_939_;
}
}
}
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
lean_del_object(v___x_763_);
v___x_967_ = lean_nat_add(v___x_907_, v_size_908_);
v___x_968_ = lean_nat_add(v___x_967_, v_size_909_);
lean_dec(v_size_909_);
v___x_969_ = lean_nat_add(v___x_967_, v_size_925_);
lean_dec(v___x_967_);
lean_inc_ref(v_l_760_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v_l_912_);
lean_ctor_set(v___x_923_, 3, v_l_760_);
lean_ctor_set(v___x_923_, 2, v_v_759_);
lean_ctor_set(v___x_923_, 1, v_k_758_);
lean_ctor_set(v___x_923_, 0, v___x_969_);
v___x_971_ = v___x_923_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_760_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_l_912_);
v___x_971_ = v_reuseFailAlloc_984_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
v_isSharedCheck_978_ = !lean_is_exclusive(v_l_760_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_979_ = lean_ctor_get(v_l_760_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_760_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_760_, 2);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_l_760_, 1);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_l_760_, 0);
lean_dec(v_unused_983_);
v___x_973_ = v_l_760_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_dec(v_l_760_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 4, v_r_913_);
lean_ctor_set(v___x_973_, 3, v___x_971_);
lean_ctor_set(v___x_973_, 2, v_v_911_);
lean_ctor_set(v___x_973_, 1, v_k_910_);
lean_ctor_set(v___x_973_, 0, v___x_968_);
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_r_913_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_991_; 
v_l_991_ = lean_ctor_get(v_impl_906_, 3);
lean_inc(v_l_991_);
if (lean_obj_tag(v_l_991_) == 0)
{
lean_object* v_r_992_; lean_object* v_k_993_; lean_object* v_v_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1017_; 
v_r_992_ = lean_ctor_get(v_impl_906_, 4);
v_k_993_ = lean_ctor_get(v_impl_906_, 1);
v_v_994_ = lean_ctor_get(v_impl_906_, 2);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1018_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_1019_);
v___x_996_ = v_impl_906_;
v_isShared_997_ = v_isSharedCheck_1017_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_r_992_);
lean_inc(v_v_994_);
lean_inc(v_k_993_);
lean_dec(v_impl_906_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1017_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_k_998_; lean_object* v_v_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1013_; 
v_k_998_ = lean_ctor_get(v_l_991_, 1);
v_v_999_ = lean_ctor_get(v_l_991_, 2);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_l_991_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; 
v_unused_1014_ = lean_ctor_get(v_l_991_, 4);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_l_991_, 3);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_l_991_, 0);
lean_dec(v_unused_1016_);
v___x_1001_ = v_l_991_;
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_v_999_);
lean_inc(v_k_998_);
lean_dec(v_l_991_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_992_, 2);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v_r_992_);
lean_ctor_set(v___x_1001_, 3, v_r_992_);
lean_ctor_set(v___x_1001_, 2, v_v_759_);
lean_ctor_set(v___x_1001_, 1, v_k_758_);
lean_ctor_set(v___x_1001_, 0, v___x_907_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_r_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_r_992_);
v___x_1005_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
lean_inc(v_r_992_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 3, v_r_992_);
lean_ctor_set(v___x_996_, 0, v___x_907_);
v___x_1007_ = v___x_996_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_993_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_v_994_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_r_992_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_992_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v___x_1007_);
lean_ctor_set(v___x_763_, 3, v___x_1005_);
lean_ctor_set(v___x_763_, 2, v_v_999_);
lean_ctor_set(v___x_763_, 1, v_k_998_);
lean_ctor_set(v___x_763_, 0, v___x_1003_);
v___x_1009_ = v___x_763_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_999_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
else
{
lean_object* v_r_1020_; 
v_r_1020_ = lean_ctor_get(v_impl_906_, 4);
lean_inc(v_r_1020_);
if (lean_obj_tag(v_r_1020_) == 0)
{
lean_object* v_k_1021_; lean_object* v_v_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1033_; 
v_k_1021_ = lean_ctor_get(v_impl_906_, 1);
v_v_1022_ = lean_ctor_get(v_impl_906_, 2);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_impl_906_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; 
v_unused_1034_ = lean_ctor_get(v_impl_906_, 4);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_impl_906_, 3);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_impl_906_, 0);
lean_dec(v_unused_1036_);
v___x_1024_ = v_impl_906_;
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_v_1022_);
lean_inc(v_k_1021_);
lean_dec(v_impl_906_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(3u);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v_l_991_);
lean_ctor_set(v___x_1024_, 2, v_v_759_);
lean_ctor_set(v___x_1024_, 1, v_k_758_);
lean_ctor_set(v___x_1024_, 0, v___x_907_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_l_991_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v_l_991_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_r_1020_);
lean_ctor_set(v___x_763_, 3, v___x_1028_);
lean_ctor_set(v___x_763_, 2, v_v_1022_);
lean_ctor_set(v___x_763_, 1, v_k_1021_);
lean_ctor_set(v___x_763_, 0, v___x_1026_);
v___x_1030_ = v___x_763_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_k_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_v_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_r_1020_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_unsigned_to_nat(2u);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_impl_906_);
lean_ctor_set(v___x_763_, 3, v_r_1020_);
lean_ctor_set(v___x_763_, 0, v___x_1037_);
v___x_1039_ = v___x_763_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_r_1020_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_impl_906_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
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
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_k_754_);
lean_ctor_set(v___x_1043_, 2, v_v_755_);
lean_ctor_set(v___x_1043_, 3, v_t_756_);
lean_ctor_set(v___x_1043_, 4, v_t_756_);
return v___x_1043_;
}
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = lean_box(1);
v___x_1045_ = l_Lake_ExternLib_defaultFacetConfig;
v___x_1046_ = l_Lake_ExternLib_defaultFacet;
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1046_, v___x_1045_, v___x_1044_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1048_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__0, &l_Lake_ExternLib_initFacetConfigs___closed__0_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__0);
v___x_1049_ = l_Lake_ExternLib_staticFacetConfig;
v___x_1050_ = l_Lake_ExternLib_staticFacet;
v___x_1051_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1050_, v___x_1049_, v___x_1048_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__1, &l_Lake_ExternLib_initFacetConfigs___closed__1_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__1);
v___x_1053_ = l_Lake_ExternLib_sharedFacetConfig;
v___x_1054_ = l_Lake_ExternLib_sharedFacet;
v___x_1055_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1054_, v___x_1053_, v___x_1052_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__2, &l_Lake_ExternLib_initFacetConfigs___closed__2_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__2);
v___x_1057_ = l_Lake_ExternLib_dynlibFacetConfig;
v___x_1058_ = l_Lake_ExternLib_dynlibFacet;
v___x_1059_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1058_, v___x_1057_, v___x_1056_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__3, &l_Lake_ExternLib_initFacetConfigs___closed__3_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__3);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_1061_, lean_object* v_k_1062_, lean_object* v_v_1063_, lean_object* v_t_1064_, lean_object* v_hl_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_1062_, v_v_1063_, v_t_1064_);
return v___x_1066_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_ExternLib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_ExternLib_staticFacetConfig = _init_l_Lake_ExternLib_staticFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_staticFacetConfig);
l_Lake_ExternLib_sharedFacetConfig = _init_l_Lake_ExternLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_sharedFacetConfig);
l_Lake_ExternLib_dynlibFacetConfig = _init_l_Lake_ExternLib_dynlibFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_dynlibFacetConfig);
l_Lake_ExternLib_defaultFacetConfig = _init_l_Lake_ExternLib_defaultFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_defaultFacetConfig);
l_Lake_ExternLib_initFacetConfigs = _init_l_Lake_ExternLib_initFacetConfigs();
lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_ExternLib(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Build_Common(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_ExternLib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_ExternLib(builtin);
}
#ifdef __cplusplus
}
#endif
