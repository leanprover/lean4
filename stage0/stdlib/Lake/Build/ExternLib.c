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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3;
static const lean_array_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_value;
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
v_registeredJobs_71_ = lean_ctor_get(v_a_47_, 4);
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
v___x_80_ = lean_st_ref_put(v_registeredJobs_71_, v___x_79_);
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
lean_object* v_log_282_; uint8_t v_action_283_; uint8_t v_wantsRebuild_284_; lean_object* v_trace_285_; lean_object* v_buildTime_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_339_; 
v_log_282_ = lean_ctor_get(v___y_280_, 0);
v_action_283_ = lean_ctor_get_uint8(v___y_280_, sizeof(void*)*3);
v_wantsRebuild_284_ = lean_ctor_get_uint8(v___y_280_, sizeof(void*)*3 + 1);
v_trace_285_ = lean_ctor_get(v___y_280_, 1);
v_buildTime_286_ = lean_ctor_get(v___y_280_, 2);
v_isSharedCheck_339_ = !lean_is_exclusive(v___y_280_);
if (v_isSharedCheck_339_ == 0)
{
v___x_288_ = v___y_280_;
v_isShared_289_ = v_isSharedCheck_339_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_buildTime_286_);
lean_inc(v_trace_285_);
lean_inc(v_log_282_);
lean_dec(v___y_280_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_339_;
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
size_t v___x_336_; size_t v___x_337_; uint64_t v___x_338_; 
v___x_336_ = ((size_t)0ULL);
v___x_337_ = lean_usize_of_nat(v___x_334_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_272_, v___x_336_, v___x_337_, v___x_332_);
v___y_293_ = v___x_338_;
goto v___jp_292_;
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
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object* v_traceArgs_340_, lean_object* v_weakArgs_341_, lean_object* v_staticLib_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lake_buildLeanSharedLibOfStatic___lam__1(v_traceArgs_340_, v_weakArgs_341_, v_staticLib_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec(v___y_345_);
lean_dec(v___y_344_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* v_staticLibJob_351_, lean_object* v_weakArgs_352_, lean_object* v_traceArgs_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; 
v___f_361_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed), 10, 2);
lean_closure_set(v___f_361_, 0, v_traceArgs_353_);
lean_closure_set(v___f_361_, 1, v_weakArgs_352_);
v___x_362_ = l_Lake_instDataKindFilePath;
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = 0;
v___x_365_ = l_Lake_Job_mapM___redArg(v___x_362_, v_staticLibJob_351_, v___f_361_, v___x_363_, v___x_364_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object* v_staticLibJob_366_, lean_object* v_weakArgs_367_, lean_object* v_traceArgs_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lake_buildLeanSharedLibOfStatic(v_staticLibJob_366_, v_weakArgs_367_, v_traceArgs_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec_ref(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec(v_a_371_);
lean_dec(v_a_370_);
return v_res_376_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1));
v___x_381_ = l_Lake_BuildTrace_nil(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object* v___x_382_, lean_object* v_config_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
lean_inc_ref(v___y_384_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc(v___y_386_);
lean_inc(v___y_385_);
v___x_391_ = lean_apply_7(v___y_384_, v___x_382_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, lean_box(0));
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_toLeanConfig_392_; lean_object* v_a_393_; lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_405_; 
v_toLeanConfig_392_ = lean_ctor_get(v_config_383_, 1);
lean_inc_ref(v_toLeanConfig_392_);
lean_dec_ref(v_config_383_);
v_a_393_ = lean_ctor_get(v___x_391_, 0);
v_a_394_ = lean_ctor_get(v___x_391_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_405_ == 0)
{
v___x_396_ = v___x_391_;
v_isShared_397_ = v_isSharedCheck_405_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_inc(v_a_393_);
lean_dec(v___x_391_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_405_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_moreLinkArgs_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v_moreLinkArgs_398_ = lean_ctor_get(v_toLeanConfig_392_, 8);
lean_inc_ref(v_moreLinkArgs_398_);
lean_dec_ref(v_toLeanConfig_392_);
v___x_399_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0));
v___x_400_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_401_ = l_Lake_buildLeanSharedLibOfStatic(v_a_393_, v_moreLinkArgs_398_, v___x_399_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___x_400_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_401_);
v___x_403_ = v___x_396_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_a_394_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
else
{
lean_dec_ref(v___y_384_);
lean_dec_ref(v_config_383_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object* v___x_406_, lean_object* v_config_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(v___x_406_, v_config_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec(v___y_410_);
lean_dec(v___y_409_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object* v_lib_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_pkg_425_; lean_object* v_name_426_; lean_object* v_keyName_427_; lean_object* v_config_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___f_434_; lean_object* v___x_435_; 
v_pkg_425_ = lean_ctor_get(v_lib_417_, 0);
v_name_426_ = lean_ctor_get(v_lib_417_, 1);
lean_inc_n(v_name_426_, 2);
v_keyName_427_ = lean_ctor_get(v_pkg_425_, 2);
v_config_428_ = lean_ctor_get(v_pkg_425_, 6);
lean_inc_ref(v_config_428_);
v___x_429_ = l_Lake_instDataKindFilePath;
v___x_430_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_keyName_427_);
v___x_431_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_431_, 0, v_keyName_427_);
lean_ctor_set(v___x_431_, 1, v_name_426_);
v___x_432_ = l_Lake_ExternLib_keyword;
v___x_433_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
lean_ctor_set(v___x_433_, 2, v_lib_417_);
lean_ctor_set(v___x_433_, 3, v___x_430_);
v___f_434_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed), 9, 2);
lean_closure_set(v___f_434_, 0, v___x_433_);
lean_closure_set(v___f_434_, 1, v_config_428_);
v___x_435_ = l_Lake_ensureJob___redArg(v___x_429_, v___f_434_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_467_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_a_437_ = lean_ctor_get(v___x_435_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_467_ == 0)
{
v___x_439_ = v___x_435_;
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_task_441_; lean_object* v_kind_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_465_; 
v_task_441_ = lean_ctor_get(v_a_436_, 0);
v_kind_442_ = lean_ctor_get(v_a_436_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_436_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_a_436_, 2);
lean_dec(v_unused_466_);
v___x_444_ = v_a_436_;
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_kind_442_);
lean_inc(v_task_441_);
lean_dec(v_a_436_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_registeredJobs_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v_job_456_; 
v_registeredJobs_446_ = lean_ctor_get(v_a_422_, 4);
v___x_447_ = lean_st_ref_take(v_registeredJobs_446_);
v___x_448_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_449_ = l_Lean_Name_str___override(v_name_426_, v___x_448_);
v___x_450_ = 1;
v___x_451_ = l_Lean_Name_toString(v___x_449_, v___x_450_);
v___x_452_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0));
v___x_453_ = lean_string_append(v___x_451_, v___x_452_);
v___x_454_ = 0;
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 2, v___x_453_);
v_job_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_task_441_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_kind_442_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___x_453_);
v_job_456_ = v_reuseFailAlloc_464_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_ctor_set_uint8(v_job_456_, sizeof(void*)*3, v___x_454_);
lean_inc_ref(v_job_456_);
v___x_457_ = l_Lake_Job_toOpaque___redArg(v_job_456_);
v___x_458_ = lean_array_push(v___x_447_, v___x_457_);
v___x_459_ = lean_st_ref_put(v_registeredJobs_446_, v___x_458_);
v___x_460_ = l_Lake_Job_renew___redArg(v_job_456_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_460_);
v___x_462_ = v___x_439_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_a_437_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
else
{
lean_dec(v_name_426_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object* v_lib_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(v_lib_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec(v_a_471_);
lean_dec(v_a_470_);
return v_res_476_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___f_478_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_479_ = 1;
v___x_480_ = l_Lake_instDataKindFilePath;
v___x_481_ = ((lean_object*)(l_Lake_ExternLib_sharedFacetConfig___closed__0));
v___x_482_ = l_Lake_ExternLib_keyword;
v___x_483_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 2, v___x_480_);
lean_ctor_set(v___x_483_, 3, v___f_478_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*4, v___x_479_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*4 + 1, v___x_479_);
return v___x_483_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lake_ExternLib_sharedFacetConfig___closed__1, &l_Lake_ExternLib_sharedFacetConfig___closed__1_once, _init_l_Lake_ExternLib_sharedFacetConfig___closed__1);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_489_ = lean_string_utf8_byte_size(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object* v_sharedLib_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_523_; 
lean_inc_ref(v_sharedLib_493_);
v___x_523_ = l_System_FilePath_fileStem(v_sharedLib_493_);
if (lean_obj_tag(v___x_523_) == 1)
{
lean_object* v_val_524_; uint8_t v___x_525_; 
v_val_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_System_Platform_isWindows;
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_526_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_527_ = lean_string_utf8_byte_size(v_val_524_);
v___x_528_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3, &l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_once, _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3);
v___x_529_ = lean_nat_dec_le(v___x_528_, v___x_527_);
if (v___x_529_ == 0)
{
lean_dec(v_val_524_);
goto v___jp_501_;
}
else
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_string_memcmp(v_val_524_, v___x_526_, v___x_530_, v___x_530_, v___x_528_);
if (v___x_531_ == 0)
{
lean_dec(v_val_524_);
goto v___jp_501_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_532_ = lean_unsigned_to_nat(3u);
lean_inc(v_val_524_);
v___x_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_533_, 0, v_val_524_);
lean_ctor_set(v___x_533_, 1, v___x_530_);
lean_ctor_set(v___x_533_, 2, v___x_527_);
v___x_534_ = l_String_Slice_Pos_nextn(v___x_533_, v___x_530_, v___x_532_);
lean_dec_ref_known(v___x_533_, 3);
v___x_535_ = lean_string_utf8_extract_fast(v_val_524_, v___x_534_, v___x_527_);
lean_dec(v___x_534_);
lean_dec(v_val_524_);
v___x_536_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4));
v___x_537_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_537_, 0, v_sharedLib_493_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_536_);
lean_ctor_set(v___x_537_, 3, v___x_536_);
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*4, v___x_525_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___y_499_);
return v___x_538_;
}
}
}
else
{
uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = 0;
v___x_540_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4));
v___x_541_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_541_, 0, v_sharedLib_493_);
lean_ctor_set(v___x_541_, 1, v_val_524_);
lean_ctor_set(v___x_541_, 2, v___x_540_);
lean_ctor_set(v___x_541_, 3, v___x_540_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*4, v___x_539_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_499_);
return v___x_542_;
}
}
else
{
lean_object* v_log_543_; uint8_t v_action_544_; uint8_t v_wantsRebuild_545_; lean_object* v_trace_546_; lean_object* v_buildTime_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_563_; 
lean_dec(v___x_523_);
v_log_543_ = lean_ctor_get(v___y_499_, 0);
v_action_544_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*3);
v_wantsRebuild_545_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*3 + 1);
v_trace_546_ = lean_ctor_get(v___y_499_, 1);
v_buildTime_547_ = lean_ctor_get(v___y_499_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v___y_499_);
if (v_isSharedCheck_563_ == 0)
{
v___x_549_ = v___y_499_;
v_isShared_550_ = v_isSharedCheck_563_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_buildTime_547_);
lean_inc(v_trace_546_);
lean_inc(v_log_543_);
lean_dec(v___y_499_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_563_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_551_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_552_ = lean_string_append(v___x_551_, v_sharedLib_493_);
lean_dec_ref(v_sharedLib_493_);
v___x_553_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5));
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
v___x_555_ = 3;
v___x_556_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_555_);
v___x_557_ = lean_array_get_size(v_log_543_);
v___x_558_ = lean_array_push(v_log_543_, v___x_556_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_558_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_trace_546_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_buildTime_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*3, v_action_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*3 + 1, v_wantsRebuild_545_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_557_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
}
}
v___jp_501_:
{
lean_object* v_log_502_; uint8_t v_action_503_; uint8_t v_wantsRebuild_504_; lean_object* v_trace_505_; lean_object* v_buildTime_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_522_; 
v_log_502_ = lean_ctor_get(v___y_499_, 0);
v_action_503_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*3);
v_wantsRebuild_504_ = lean_ctor_get_uint8(v___y_499_, sizeof(void*)*3 + 1);
v_trace_505_ = lean_ctor_get(v___y_499_, 1);
v_buildTime_506_ = lean_ctor_get(v___y_499_, 2);
v_isSharedCheck_522_ = !lean_is_exclusive(v___y_499_);
if (v_isSharedCheck_522_ == 0)
{
v___x_508_ = v___y_499_;
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_buildTime_506_);
lean_inc(v_trace_505_);
lean_inc(v_log_502_);
lean_dec(v___y_499_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_510_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_511_ = lean_string_append(v___x_510_, v_sharedLib_493_);
lean_dec_ref(v_sharedLib_493_);
v___x_512_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
v___x_514_ = 3;
v___x_515_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_514_);
v___x_516_ = lean_array_get_size(v_log_502_);
v___x_517_ = lean_array_push(v_log_502_, v___x_515_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_517_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_trace_505_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_buildTime_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_521_, sizeof(void*)*3, v_action_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_521_, sizeof(void*)*3 + 1, v_wantsRebuild_504_);
v___x_519_ = v_reuseFailAlloc_521_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_516_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object* v_sharedLib_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(v_sharedLib_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object* v_sharedLibTarget_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v___f_582_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0));
v___x_583_ = l_Lake_instDataKindDynlib;
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = 0;
v___x_586_ = l_Lake_Job_mapM___redArg(v___x_583_, v_sharedLibTarget_574_, v___f_582_, v___x_584_, v___x_585_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object* v_sharedLibTarget_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_sharedLibTarget_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec_ref(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec(v_a_590_);
lean_dec(v_a_589_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object* v___x_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; 
lean_inc_ref(v___y_597_);
lean_inc_ref(v___y_601_);
lean_inc(v___y_600_);
lean_inc(v___y_599_);
lean_inc(v___y_598_);
v___x_604_ = lean_apply_7(v___y_597_, v___x_596_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, lean_box(0));
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_a_606_ = lean_ctor_get(v___x_604_, 1);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_615_ == 0)
{
v___x_608_ = v___x_604_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_610_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_611_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_a_605_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___x_610_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_a_606_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
lean_object* v_a_616_; lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v___y_597_);
v_a_616_ = lean_ctor_get(v___x_604_, 0);
v_a_617_ = lean_ctor_get(v___x_604_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_604_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_inc(v_a_616_);
lean_dec(v___x_604_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_616_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object* v___x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(v___x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec(v___y_628_);
lean_dec(v___y_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object* v_lib_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_pkg_643_; lean_object* v_name_644_; lean_object* v_keyName_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___x_652_; 
v_pkg_643_ = lean_ctor_get(v_lib_635_, 0);
v_name_644_ = lean_ctor_get(v_lib_635_, 1);
lean_inc_n(v_name_644_, 2);
v_keyName_645_ = lean_ctor_get(v_pkg_643_, 2);
v___x_646_ = l_Lake_instDataKindDynlib;
v___x_647_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_keyName_645_);
v___x_648_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_648_, 0, v_keyName_645_);
lean_ctor_set(v___x_648_, 1, v_name_644_);
v___x_649_ = l_Lake_ExternLib_keyword;
v___x_650_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
lean_ctor_set(v___x_650_, 2, v_lib_635_);
lean_ctor_set(v___x_650_, 3, v___x_647_);
v___f_651_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed), 8, 1);
lean_closure_set(v___f_651_, 0, v___x_650_);
v___x_652_ = l_Lake_ensureJob___redArg(v___x_646_, v___f_651_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_684_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_a_654_ = lean_ctor_get(v___x_652_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_684_ == 0)
{
v___x_656_ = v___x_652_;
v_isShared_657_ = v_isSharedCheck_684_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_684_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_task_658_; lean_object* v_kind_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_682_; 
v_task_658_ = lean_ctor_get(v_a_653_, 0);
v_kind_659_ = lean_ctor_get(v_a_653_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_a_653_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v_a_653_, 2);
lean_dec(v_unused_683_);
v___x_661_ = v_a_653_;
v_isShared_662_ = v_isSharedCheck_682_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_kind_659_);
lean_inc(v_task_658_);
lean_dec(v_a_653_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_682_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_registeredJobs_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v_job_673_; 
v_registeredJobs_663_ = lean_ctor_get(v_a_640_, 4);
v___x_664_ = lean_st_ref_take(v_registeredJobs_663_);
v___x_665_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_666_ = l_Lean_Name_str___override(v_name_644_, v___x_665_);
v___x_667_ = 1;
v___x_668_ = l_Lean_Name_toString(v___x_666_, v___x_667_);
v___x_669_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0));
v___x_670_ = lean_string_append(v___x_668_, v___x_669_);
v___x_671_ = 0;
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 2, v___x_670_);
v_job_673_ = v___x_661_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_task_658_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_kind_659_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v___x_670_);
v_job_673_ = v_reuseFailAlloc_681_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
lean_ctor_set_uint8(v_job_673_, sizeof(void*)*3, v___x_671_);
lean_inc_ref(v_job_673_);
v___x_674_ = l_Lake_Job_toOpaque___redArg(v_job_673_);
v___x_675_ = lean_array_push(v___x_664_, v___x_674_);
v___x_676_ = lean_st_ref_put(v_registeredJobs_663_, v___x_675_);
v___x_677_ = l_Lake_Job_renew___redArg(v_job_673_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_677_);
v___x_679_ = v___x_656_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_a_654_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_dec(v_name_644_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object* v_lib_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(v_lib_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec(v_a_688_);
lean_dec(v_a_687_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t v_fmt_694_, lean_object* v_a_695_){
_start:
{
if (v_fmt_694_ == 0)
{
lean_object* v_path_696_; 
v_path_696_ = lean_ctor_get(v_a_695_, 0);
lean_inc_ref(v_path_696_);
return v_path_696_;
}
else
{
lean_object* v_path_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_path_697_ = lean_ctor_get(v_a_695_, 0);
lean_inc_ref(v_path_697_);
v___x_698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_698_, 0, v_path_697_);
v___x_699_ = l_Lean_Json_compress(v___x_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object* v_fmt_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_fmt_boxed_702_; lean_object* v_res_703_; 
v_fmt_boxed_702_ = lean_unbox(v_fmt_700_);
v_res_703_ = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(v_fmt_boxed_702_, v_a_701_);
lean_dec_ref(v_a_701_);
return v_res_703_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___f_706_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__0));
v___x_707_ = 1;
v___x_708_ = l_Lake_instDataKindDynlib;
v___x_709_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__1));
v___x_710_ = l_Lake_ExternLib_keyword;
v___x_711_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_708_);
lean_ctor_set(v___x_711_, 3, v___f_706_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*4, v___x_707_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*4 + 1, v___x_707_);
return v___x_711_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig(void){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l_Lake_ExternLib_dynlibFacetConfig___closed__2, &l_Lake_ExternLib_dynlibFacetConfig___closed__2_once, _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object* v_lib_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_pkg_721_; lean_object* v_name_722_; lean_object* v_keyName_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_pkg_721_ = lean_ctor_get(v_lib_713_, 0);
v_name_722_ = lean_ctor_get(v_lib_713_, 1);
v_keyName_723_ = lean_ctor_get(v_pkg_721_, 2);
v___x_724_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_722_);
lean_inc(v_keyName_723_);
v___x_725_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_725_, 0, v_keyName_723_);
lean_ctor_set(v___x_725_, 1, v_name_722_);
v___x_726_ = l_Lake_ExternLib_keyword;
v___x_727_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
lean_ctor_set(v___x_727_, 2, v_lib_713_);
lean_ctor_set(v___x_727_, 3, v___x_724_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc(v_a_716_);
lean_inc(v_a_715_);
v___x_728_ = lean_apply_7(v_a_714_, v___x_727_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, lean_box(0));
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object* v_lib_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(v_lib_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec(v_a_732_);
lean_dec(v_a_731_);
return v_res_737_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_739_; lean_object* v___f_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_739_ = 0;
v___f_740_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_741_ = 1;
v___x_742_ = l_Lake_instDataKindFilePath;
v___x_743_ = ((lean_object*)(l_Lake_ExternLib_defaultFacetConfig___closed__0));
v___x_744_ = l_Lake_ExternLib_keyword;
v___x_745_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_743_);
lean_ctor_set(v___x_745_, 2, v___x_742_);
lean_ctor_set(v___x_745_, 3, v___f_740_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*4, v___x_741_);
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*4 + 1, v___x_739_);
return v___x_745_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&l_Lake_ExternLib_defaultFacetConfig___closed__1, &l_Lake_ExternLib_defaultFacetConfig___closed__1_once, _init_l_Lake_ExternLib_defaultFacetConfig___closed__1);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_747_, lean_object* v_v_748_, lean_object* v_t_749_){
_start:
{
if (lean_obj_tag(v_t_749_) == 0)
{
lean_object* v_size_750_; lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v_l_753_; lean_object* v_r_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_1034_; 
v_size_750_ = lean_ctor_get(v_t_749_, 0);
v_k_751_ = lean_ctor_get(v_t_749_, 1);
v_v_752_ = lean_ctor_get(v_t_749_, 2);
v_l_753_ = lean_ctor_get(v_t_749_, 3);
v_r_754_ = lean_ctor_get(v_t_749_, 4);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_t_749_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_756_ = v_t_749_;
v_isShared_757_ = v_isSharedCheck_1034_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_r_754_);
lean_inc(v_l_753_);
lean_inc(v_v_752_);
lean_inc(v_k_751_);
lean_inc(v_size_750_);
lean_dec(v_t_749_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_1034_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
uint8_t v___x_758_; 
v___x_758_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_747_, v_k_751_);
switch(v___x_758_)
{
case 0:
{
lean_object* v_impl_759_; lean_object* v___x_760_; 
lean_dec(v_size_750_);
v_impl_759_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_747_, v_v_748_, v_l_753_);
v___x_760_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_754_) == 0)
{
lean_object* v_size_761_; lean_object* v_size_762_; lean_object* v_k_763_; lean_object* v_v_764_; lean_object* v_l_765_; lean_object* v_r_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_size_761_ = lean_ctor_get(v_r_754_, 0);
v_size_762_ = lean_ctor_get(v_impl_759_, 0);
lean_inc(v_size_762_);
v_k_763_ = lean_ctor_get(v_impl_759_, 1);
lean_inc(v_k_763_);
v_v_764_ = lean_ctor_get(v_impl_759_, 2);
lean_inc(v_v_764_);
v_l_765_ = lean_ctor_get(v_impl_759_, 3);
lean_inc(v_l_765_);
v_r_766_ = lean_ctor_get(v_impl_759_, 4);
lean_inc(v_r_766_);
v___x_767_ = lean_unsigned_to_nat(3u);
v___x_768_ = lean_nat_mul(v___x_767_, v_size_761_);
v___x_769_ = lean_nat_dec_lt(v___x_768_, v_size_762_);
lean_dec(v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec(v_r_766_);
lean_dec(v_l_765_);
lean_dec(v_v_764_);
lean_dec(v_k_763_);
v___x_770_ = lean_nat_add(v___x_760_, v_size_762_);
lean_dec(v_size_762_);
v___x_771_ = lean_nat_add(v___x_770_, v_size_761_);
lean_dec(v___x_770_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 3, v_impl_759_);
lean_ctor_set(v___x_756_, 0, v___x_771_);
v___x_773_ = v___x_756_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_impl_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_r_754_);
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
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_840_; 
v_isSharedCheck_840_ = !lean_is_exclusive(v_impl_759_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_841_ = lean_ctor_get(v_impl_759_, 4);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_impl_759_, 3);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_impl_759_, 2);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_impl_759_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_impl_759_, 0);
lean_dec(v_unused_845_);
v___x_776_ = v_impl_759_;
v_isShared_777_ = v_isSharedCheck_840_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_impl_759_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_840_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_size_778_; lean_object* v_size_779_; lean_object* v_k_780_; lean_object* v_v_781_; lean_object* v_l_782_; lean_object* v_r_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v_size_778_ = lean_ctor_get(v_l_765_, 0);
v_size_779_ = lean_ctor_get(v_r_766_, 0);
v_k_780_ = lean_ctor_get(v_r_766_, 1);
v_v_781_ = lean_ctor_get(v_r_766_, 2);
v_l_782_ = lean_ctor_get(v_r_766_, 3);
v_r_783_ = lean_ctor_get(v_r_766_, 4);
v___x_784_ = lean_unsigned_to_nat(2u);
v___x_785_ = lean_nat_mul(v___x_784_, v_size_778_);
v___x_786_ = lean_nat_dec_lt(v_size_779_, v___x_785_);
lean_dec(v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_815_; 
lean_inc(v_r_783_);
lean_inc(v_l_782_);
lean_inc(v_v_781_);
lean_inc(v_k_780_);
v_isSharedCheck_815_ = !lean_is_exclusive(v_r_766_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_816_ = lean_ctor_get(v_r_766_, 4);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_r_766_, 3);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_r_766_, 2);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_r_766_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_r_766_, 0);
lean_dec(v_unused_820_);
v___x_788_ = v_r_766_;
v_isShared_789_ = v_isSharedCheck_815_;
goto v_resetjp_787_;
}
else
{
lean_dec(v_r_766_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_815_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___x_803_; lean_object* v___y_805_; 
v___x_790_ = lean_nat_add(v___x_760_, v_size_762_);
lean_dec(v_size_762_);
v___x_791_ = lean_nat_add(v___x_790_, v_size_761_);
lean_dec(v___x_790_);
v___x_803_ = lean_nat_add(v___x_760_, v_size_778_);
if (lean_obj_tag(v_l_782_) == 0)
{
lean_object* v_size_813_; 
v_size_813_ = lean_ctor_get(v_l_782_, 0);
lean_inc(v_size_813_);
v___y_805_ = v_size_813_;
goto v___jp_804_;
}
else
{
lean_object* v___x_814_; 
v___x_814_ = lean_unsigned_to_nat(0u);
v___y_805_ = v___x_814_;
goto v___jp_804_;
}
v___jp_792_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_nat_add(v___y_793_, v___y_795_);
lean_dec(v___y_795_);
lean_dec(v___y_793_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 4, v_r_754_);
lean_ctor_set(v___x_788_, 3, v_r_783_);
lean_ctor_set(v___x_788_, 2, v_v_752_);
lean_ctor_set(v___x_788_, 1, v_k_751_);
lean_ctor_set(v___x_788_, 0, v___x_796_);
v___x_798_ = v___x_788_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_r_783_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_r_754_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 4, v___x_798_);
lean_ctor_set(v___x_776_, 3, v___y_794_);
lean_ctor_set(v___x_776_, 2, v_v_781_);
lean_ctor_set(v___x_776_, 1, v_k_780_);
lean_ctor_set(v___x_776_, 0, v___x_791_);
v___x_800_ = v___x_776_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v___y_794_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
v___jp_804_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_nat_add(v___x_803_, v___y_805_);
lean_dec(v___y_805_);
lean_dec(v___x_803_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_l_782_);
lean_ctor_set(v___x_756_, 3, v_l_765_);
lean_ctor_set(v___x_756_, 2, v_v_764_);
lean_ctor_set(v___x_756_, 1, v_k_763_);
lean_ctor_set(v___x_756_, 0, v___x_806_);
v___x_808_ = v___x_756_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_763_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_764_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v_l_765_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v_l_782_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_nat_add(v___x_760_, v_size_761_);
if (lean_obj_tag(v_r_783_) == 0)
{
lean_object* v_size_810_; 
v_size_810_ = lean_ctor_get(v_r_783_, 0);
lean_inc(v_size_810_);
v___y_793_ = v___x_809_;
v___y_794_ = v___x_808_;
v___y_795_ = v_size_810_;
goto v___jp_792_;
}
else
{
lean_object* v___x_811_; 
v___x_811_ = lean_unsigned_to_nat(0u);
v___y_793_ = v___x_809_;
v___y_794_ = v___x_808_;
v___y_795_ = v___x_811_;
goto v___jp_792_;
}
}
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_del_object(v___x_756_);
v___x_821_ = lean_nat_add(v___x_760_, v_size_762_);
lean_dec(v_size_762_);
v___x_822_ = lean_nat_add(v___x_821_, v_size_761_);
lean_dec(v___x_821_);
v___x_823_ = lean_nat_add(v___x_760_, v_size_761_);
v___x_824_ = lean_nat_add(v___x_823_, v_size_779_);
lean_dec(v___x_823_);
lean_inc_ref(v_r_754_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 4, v_r_754_);
lean_ctor_set(v___x_776_, 3, v_r_766_);
lean_ctor_set(v___x_776_, 2, v_v_752_);
lean_ctor_set(v___x_776_, 1, v_k_751_);
lean_ctor_set(v___x_776_, 0, v___x_824_);
v___x_826_ = v___x_776_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_r_766_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_r_754_);
v___x_826_ = v_reuseFailAlloc_839_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v_r_754_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_834_ = lean_ctor_get(v_r_754_, 4);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_754_, 3);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_r_754_, 2);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_r_754_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_r_754_, 0);
lean_dec(v_unused_838_);
v___x_828_ = v_r_754_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_r_754_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 4, v___x_826_);
lean_ctor_set(v___x_828_, 3, v_l_765_);
lean_ctor_set(v___x_828_, 2, v_v_764_);
lean_ctor_set(v___x_828_, 1, v_k_763_);
lean_ctor_set(v___x_828_, 0, v___x_822_);
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_763_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_v_764_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_l_765_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___x_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_846_; 
v_l_846_ = lean_ctor_get(v_impl_759_, 3);
lean_inc(v_l_846_);
if (lean_obj_tag(v_l_846_) == 0)
{
lean_object* v_r_847_; lean_object* v_k_848_; lean_object* v_v_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_860_; 
v_r_847_ = lean_ctor_get(v_impl_759_, 4);
v_k_848_ = lean_ctor_get(v_impl_759_, 1);
v_v_849_ = lean_ctor_get(v_impl_759_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_impl_759_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; lean_object* v_unused_862_; 
v_unused_861_ = lean_ctor_get(v_impl_759_, 3);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_impl_759_, 0);
lean_dec(v_unused_862_);
v___x_851_ = v_impl_759_;
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_r_847_);
lean_inc(v_v_849_);
lean_inc(v_k_848_);
lean_dec(v_impl_759_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_847_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 3, v_r_847_);
lean_ctor_set(v___x_851_, 2, v_v_752_);
lean_ctor_set(v___x_851_, 1, v_k_751_);
lean_ctor_set(v___x_851_, 0, v___x_760_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_859_, 3, v_r_847_);
lean_ctor_set(v_reuseFailAlloc_859_, 4, v_r_847_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v___x_855_);
lean_ctor_set(v___x_756_, 3, v_l_846_);
lean_ctor_set(v___x_756_, 2, v_v_849_);
lean_ctor_set(v___x_756_, 1, v_k_848_);
lean_ctor_set(v___x_756_, 0, v___x_853_);
v___x_857_ = v___x_756_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_l_846_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_object* v_r_863_; 
v_r_863_ = lean_ctor_get(v_impl_759_, 4);
lean_inc(v_r_863_);
if (lean_obj_tag(v_r_863_) == 0)
{
lean_object* v_k_864_; lean_object* v_v_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_888_; 
v_k_864_ = lean_ctor_get(v_impl_759_, 1);
v_v_865_ = lean_ctor_get(v_impl_759_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_impl_759_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; 
v_unused_889_ = lean_ctor_get(v_impl_759_, 4);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_impl_759_, 3);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_impl_759_, 0);
lean_dec(v_unused_891_);
v___x_867_ = v_impl_759_;
v_isShared_868_ = v_isSharedCheck_888_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_v_865_);
lean_inc(v_k_864_);
lean_dec(v_impl_759_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_888_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_k_869_; lean_object* v_v_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_884_; 
v_k_869_ = lean_ctor_get(v_r_863_, 1);
v_v_870_ = lean_ctor_get(v_r_863_, 2);
v_isSharedCheck_884_ = !lean_is_exclusive(v_r_863_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; 
v_unused_885_ = lean_ctor_get(v_r_863_, 4);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_r_863_, 3);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_r_863_, 0);
lean_dec(v_unused_887_);
v___x_872_ = v_r_863_;
v_isShared_873_ = v_isSharedCheck_884_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_v_870_);
lean_inc(v_k_869_);
lean_dec(v_r_863_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_884_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_unsigned_to_nat(3u);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 4, v_l_846_);
lean_ctor_set(v___x_872_, 3, v_l_846_);
lean_ctor_set(v___x_872_, 2, v_v_865_);
lean_ctor_set(v___x_872_, 1, v_k_864_);
lean_ctor_set(v___x_872_, 0, v___x_760_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_k_864_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_v_865_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_l_846_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v_l_846_);
v___x_876_ = v_reuseFailAlloc_883_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v_l_846_);
lean_ctor_set(v___x_867_, 2, v_v_752_);
lean_ctor_set(v___x_867_, 1, v_k_751_);
lean_ctor_set(v___x_867_, 0, v___x_760_);
v___x_878_ = v___x_867_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v_l_846_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_l_846_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v___x_878_);
lean_ctor_set(v___x_756_, 3, v___x_876_);
lean_ctor_set(v___x_756_, 2, v_v_870_);
lean_ctor_set(v___x_756_, 1, v_k_869_);
lean_ctor_set(v___x_756_, 0, v___x_874_);
v___x_880_ = v___x_756_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_869_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_870_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
else
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_unsigned_to_nat(2u);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_r_863_);
lean_ctor_set(v___x_756_, 3, v_impl_759_);
lean_ctor_set(v___x_756_, 0, v___x_892_);
v___x_894_ = v___x_756_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_impl_759_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_r_863_);
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
}
case 1:
{
lean_object* v___x_897_; 
lean_dec(v_v_752_);
lean_dec(v_k_751_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 2, v_v_748_);
lean_ctor_set(v___x_756_, 1, v_k_747_);
v___x_897_ = v___x_756_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_size_750_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_k_747_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_v_748_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_l_753_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_r_754_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
default: 
{
lean_object* v_impl_899_; lean_object* v___x_900_; 
lean_dec(v_size_750_);
v_impl_899_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_747_, v_v_748_, v_r_754_);
v___x_900_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_753_) == 0)
{
lean_object* v_size_901_; lean_object* v_size_902_; lean_object* v_k_903_; lean_object* v_v_904_; lean_object* v_l_905_; lean_object* v_r_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_size_901_ = lean_ctor_get(v_l_753_, 0);
v_size_902_ = lean_ctor_get(v_impl_899_, 0);
lean_inc(v_size_902_);
v_k_903_ = lean_ctor_get(v_impl_899_, 1);
lean_inc(v_k_903_);
v_v_904_ = lean_ctor_get(v_impl_899_, 2);
lean_inc(v_v_904_);
v_l_905_ = lean_ctor_get(v_impl_899_, 3);
lean_inc(v_l_905_);
v_r_906_ = lean_ctor_get(v_impl_899_, 4);
lean_inc(v_r_906_);
v___x_907_ = lean_unsigned_to_nat(3u);
v___x_908_ = lean_nat_mul(v___x_907_, v_size_901_);
v___x_909_ = lean_nat_dec_lt(v___x_908_, v_size_902_);
lean_dec(v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec(v_r_906_);
lean_dec(v_l_905_);
lean_dec(v_v_904_);
lean_dec(v_k_903_);
v___x_910_ = lean_nat_add(v___x_900_, v_size_901_);
v___x_911_ = lean_nat_add(v___x_910_, v_size_902_);
lean_dec(v_size_902_);
lean_dec(v___x_910_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_impl_899_);
lean_ctor_set(v___x_756_, 0, v___x_911_);
v___x_913_ = v___x_756_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_l_753_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_impl_899_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_978_; 
v_isSharedCheck_978_ = !lean_is_exclusive(v_impl_899_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; lean_object* v_unused_983_; 
v_unused_979_ = lean_ctor_get(v_impl_899_, 4);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_impl_899_, 3);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_impl_899_, 2);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_impl_899_, 1);
lean_dec(v_unused_982_);
v_unused_983_ = lean_ctor_get(v_impl_899_, 0);
lean_dec(v_unused_983_);
v___x_916_ = v_impl_899_;
v_isShared_917_ = v_isSharedCheck_978_;
goto v_resetjp_915_;
}
else
{
lean_dec(v_impl_899_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_978_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_size_918_; lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v_l_921_; lean_object* v_r_922_; lean_object* v_size_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_size_918_ = lean_ctor_get(v_l_905_, 0);
v_k_919_ = lean_ctor_get(v_l_905_, 1);
v_v_920_ = lean_ctor_get(v_l_905_, 2);
v_l_921_ = lean_ctor_get(v_l_905_, 3);
v_r_922_ = lean_ctor_get(v_l_905_, 4);
v_size_923_ = lean_ctor_get(v_r_906_, 0);
v___x_924_ = lean_unsigned_to_nat(2u);
v___x_925_ = lean_nat_mul(v___x_924_, v_size_923_);
v___x_926_ = lean_nat_dec_lt(v_size_918_, v___x_925_);
lean_dec(v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_954_; 
lean_inc(v_r_922_);
lean_inc(v_l_921_);
lean_inc(v_v_920_);
lean_inc(v_k_919_);
v_isSharedCheck_954_ = !lean_is_exclusive(v_l_905_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; lean_object* v_unused_959_; 
v_unused_955_ = lean_ctor_get(v_l_905_, 4);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_905_, 3);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_905_, 2);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_l_905_, 1);
lean_dec(v_unused_958_);
v_unused_959_ = lean_ctor_get(v_l_905_, 0);
lean_dec(v_unused_959_);
v___x_928_ = v_l_905_;
v_isShared_929_ = v_isSharedCheck_954_;
goto v_resetjp_927_;
}
else
{
lean_dec(v_l_905_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_954_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_944_; 
v___x_930_ = lean_nat_add(v___x_900_, v_size_901_);
v___x_931_ = lean_nat_add(v___x_930_, v_size_902_);
lean_dec(v_size_902_);
if (lean_obj_tag(v_l_921_) == 0)
{
lean_object* v_size_952_; 
v_size_952_ = lean_ctor_get(v_l_921_, 0);
lean_inc(v_size_952_);
v___y_944_ = v_size_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = lean_unsigned_to_nat(0u);
v___y_944_ = v___x_953_;
goto v___jp_943_;
}
v___jp_932_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_nat_add(v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 4, v_r_906_);
lean_ctor_set(v___x_928_, 3, v_r_922_);
lean_ctor_set(v___x_928_, 2, v_v_904_);
lean_ctor_set(v___x_928_, 1, v_k_903_);
lean_ctor_set(v___x_928_, 0, v___x_936_);
v___x_938_ = v___x_928_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_903_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_904_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_r_922_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v_r_906_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 4, v___x_938_);
lean_ctor_set(v___x_916_, 3, v___y_933_);
lean_ctor_set(v___x_916_, 2, v_v_920_);
lean_ctor_set(v___x_916_, 1, v_k_919_);
lean_ctor_set(v___x_916_, 0, v___x_931_);
v___x_940_ = v___x_916_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v___y_933_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
v___jp_943_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_nat_add(v___x_930_, v___y_944_);
lean_dec(v___y_944_);
lean_dec(v___x_930_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_l_921_);
lean_ctor_set(v___x_756_, 0, v___x_945_);
v___x_947_ = v___x_756_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_l_753_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_l_921_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
v___x_948_ = lean_nat_add(v___x_900_, v_size_923_);
if (lean_obj_tag(v_r_922_) == 0)
{
lean_object* v_size_949_; 
v_size_949_ = lean_ctor_get(v_r_922_, 0);
lean_inc(v_size_949_);
v___y_933_ = v___x_947_;
v___y_934_ = v___x_948_;
v___y_935_ = v_size_949_;
goto v___jp_932_;
}
else
{
lean_object* v___x_950_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___y_933_ = v___x_947_;
v___y_934_ = v___x_948_;
v___y_935_ = v___x_950_;
goto v___jp_932_;
}
}
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
lean_del_object(v___x_756_);
v___x_960_ = lean_nat_add(v___x_900_, v_size_901_);
v___x_961_ = lean_nat_add(v___x_960_, v_size_902_);
lean_dec(v_size_902_);
v___x_962_ = lean_nat_add(v___x_960_, v_size_918_);
lean_dec(v___x_960_);
lean_inc_ref(v_l_753_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 4, v_l_905_);
lean_ctor_set(v___x_916_, 3, v_l_753_);
lean_ctor_set(v___x_916_, 2, v_v_752_);
lean_ctor_set(v___x_916_, 1, v_k_751_);
lean_ctor_set(v___x_916_, 0, v___x_962_);
v___x_964_ = v___x_916_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_l_753_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_l_905_);
v___x_964_ = v_reuseFailAlloc_977_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v_l_753_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; lean_object* v_unused_976_; 
v_unused_972_ = lean_ctor_get(v_l_753_, 4);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_l_753_, 3);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_l_753_, 2);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_l_753_, 1);
lean_dec(v_unused_975_);
v_unused_976_ = lean_ctor_get(v_l_753_, 0);
lean_dec(v_unused_976_);
v___x_966_ = v_l_753_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_dec(v_l_753_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 4, v_r_906_);
lean_ctor_set(v___x_966_, 3, v___x_964_);
lean_ctor_set(v___x_966_, 2, v_v_904_);
lean_ctor_set(v___x_966_, 1, v_k_903_);
lean_ctor_set(v___x_966_, 0, v___x_961_);
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_k_903_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_v_904_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v_r_906_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_984_; 
v_l_984_ = lean_ctor_get(v_impl_899_, 3);
lean_inc(v_l_984_);
if (lean_obj_tag(v_l_984_) == 0)
{
lean_object* v_r_985_; lean_object* v_k_986_; lean_object* v_v_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1010_; 
v_r_985_ = lean_ctor_get(v_impl_899_, 4);
v_k_986_ = lean_ctor_get(v_impl_899_, 1);
v_v_987_ = lean_ctor_get(v_impl_899_, 2);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_impl_899_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; lean_object* v_unused_1012_; 
v_unused_1011_ = lean_ctor_get(v_impl_899_, 3);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_impl_899_, 0);
lean_dec(v_unused_1012_);
v___x_989_ = v_impl_899_;
v_isShared_990_ = v_isSharedCheck_1010_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_r_985_);
lean_inc(v_v_987_);
lean_inc(v_k_986_);
lean_dec(v_impl_899_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1010_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_k_991_; lean_object* v_v_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1006_; 
v_k_991_ = lean_ctor_get(v_l_984_, 1);
v_v_992_ = lean_ctor_get(v_l_984_, 2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_l_984_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; lean_object* v_unused_1008_; lean_object* v_unused_1009_; 
v_unused_1007_ = lean_ctor_get(v_l_984_, 4);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v_l_984_, 3);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_l_984_, 0);
lean_dec(v_unused_1009_);
v___x_994_ = v_l_984_;
v_isShared_995_ = v_isSharedCheck_1006_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_v_992_);
lean_inc(v_k_991_);
lean_dec(v_l_984_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1006_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_996_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_985_, 2);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 4, v_r_985_);
lean_ctor_set(v___x_994_, 3, v_r_985_);
lean_ctor_set(v___x_994_, 2, v_v_752_);
lean_ctor_set(v___x_994_, 1, v_k_751_);
lean_ctor_set(v___x_994_, 0, v___x_900_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_r_985_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_r_985_);
v___x_998_ = v_reuseFailAlloc_1005_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
lean_inc(v_r_985_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 3, v_r_985_);
lean_ctor_set(v___x_989_, 0, v___x_900_);
v___x_1000_ = v___x_989_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_k_986_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_v_987_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_r_985_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_r_985_);
v___x_1000_ = v_reuseFailAlloc_1004_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v___x_1000_);
lean_ctor_set(v___x_756_, 3, v___x_998_);
lean_ctor_set(v___x_756_, 2, v_v_992_);
lean_ctor_set(v___x_756_, 1, v_k_991_);
lean_ctor_set(v___x_756_, 0, v___x_996_);
v___x_1002_ = v___x_756_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_k_991_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_v_992_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
else
{
lean_object* v_r_1013_; 
v_r_1013_ = lean_ctor_get(v_impl_899_, 4);
lean_inc(v_r_1013_);
if (lean_obj_tag(v_r_1013_) == 0)
{
lean_object* v_k_1014_; lean_object* v_v_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1026_; 
v_k_1014_ = lean_ctor_get(v_impl_899_, 1);
v_v_1015_ = lean_ctor_get(v_impl_899_, 2);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_impl_899_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; lean_object* v_unused_1028_; lean_object* v_unused_1029_; 
v_unused_1027_ = lean_ctor_get(v_impl_899_, 4);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_impl_899_, 3);
lean_dec(v_unused_1028_);
v_unused_1029_ = lean_ctor_get(v_impl_899_, 0);
lean_dec(v_unused_1029_);
v___x_1017_ = v_impl_899_;
v_isShared_1018_ = v_isSharedCheck_1026_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_v_1015_);
lean_inc(v_k_1014_);
lean_dec(v_impl_899_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1026_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = lean_unsigned_to_nat(3u);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 4, v_l_984_);
lean_ctor_set(v___x_1017_, 2, v_v_752_);
lean_ctor_set(v___x_1017_, 1, v_k_751_);
lean_ctor_set(v___x_1017_, 0, v___x_900_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_l_984_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_l_984_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_r_1013_);
lean_ctor_set(v___x_756_, 3, v___x_1021_);
lean_ctor_set(v___x_756_, 2, v_v_1015_);
lean_ctor_set(v___x_756_, 1, v_k_1014_);
lean_ctor_set(v___x_756_, 0, v___x_1019_);
v___x_1023_ = v___x_756_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_k_1014_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_v_1015_);
lean_ctor_set(v_reuseFailAlloc_1024_, 3, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_r_1013_);
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
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_unsigned_to_nat(2u);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 4, v_impl_899_);
lean_ctor_set(v___x_756_, 3, v_r_1013_);
lean_ctor_set(v___x_756_, 0, v___x_1030_);
v___x_1032_ = v___x_756_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_r_1013_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_impl_899_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
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
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v___x_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v_k_747_);
lean_ctor_set(v___x_1036_, 2, v_v_748_);
lean_ctor_set(v___x_1036_, 3, v_t_749_);
lean_ctor_set(v___x_1036_, 4, v_t_749_);
return v___x_1036_;
}
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1037_ = lean_box(1);
v___x_1038_ = l_Lake_ExternLib_defaultFacetConfig;
v___x_1039_ = l_Lake_ExternLib_defaultFacet;
v___x_1040_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1039_, v___x_1038_, v___x_1037_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__0, &l_Lake_ExternLib_initFacetConfigs___closed__0_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__0);
v___x_1042_ = l_Lake_ExternLib_staticFacetConfig;
v___x_1043_ = l_Lake_ExternLib_staticFacet;
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1043_, v___x_1042_, v___x_1041_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__1, &l_Lake_ExternLib_initFacetConfigs___closed__1_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__1);
v___x_1046_ = l_Lake_ExternLib_sharedFacetConfig;
v___x_1047_ = l_Lake_ExternLib_sharedFacet;
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1047_, v___x_1046_, v___x_1045_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__2, &l_Lake_ExternLib_initFacetConfigs___closed__2_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__2);
v___x_1050_ = l_Lake_ExternLib_dynlibFacetConfig;
v___x_1051_ = l_Lake_ExternLib_dynlibFacet;
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1051_, v___x_1050_, v___x_1049_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__3, &l_Lake_ExternLib_initFacetConfigs___closed__3_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__3);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_1054_, lean_object* v_k_1055_, lean_object* v_v_1056_, lean_object* v_t_1057_, lean_object* v_hl_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_1055_, v_v_1056_, v_t_1057_);
return v___x_1059_;
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
