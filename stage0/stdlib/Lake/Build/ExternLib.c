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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* v_pkg_50_; lean_object* v_name_51_; lean_object* v_config_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___f_61_; uint8_t v___x_62_; lean_object* v___x_63_; 
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
v___x_58_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1));
v___x_59_ = lean_string_append(v___x_57_, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v_pkg_50_);
lean_ctor_set(v___x_60_, 1, v___x_55_);
v___f_61_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed), 9, 2);
lean_closure_set(v___f_61_, 0, v___x_60_);
lean_closure_set(v___f_61_, 1, v_config_52_);
v___x_62_ = 0;
v___x_63_ = l_Lake_ensureJob___redArg(v___x_53_, v___f_61_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_88_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_a_65_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_88_ == 0)
{
v___x_67_ = v___x_63_;
v_isShared_68_ = v_isSharedCheck_88_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_88_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v_task_69_; lean_object* v_kind_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_86_; 
v_task_69_ = lean_ctor_get(v_a_64_, 0);
v_kind_70_ = lean_ctor_get(v_a_64_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_86_ == 0)
{
lean_object* v_unused_87_; 
v_unused_87_ = lean_ctor_get(v_a_64_, 2);
lean_dec(v_unused_87_);
v___x_72_ = v_a_64_;
v_isShared_73_ = v_isSharedCheck_86_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_kind_70_);
lean_inc(v_task_69_);
lean_dec(v_a_64_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_86_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_registeredJobs_74_; lean_object* v_job_76_; 
v_registeredJobs_74_ = lean_ctor_get(v_a_47_, 4);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 2, v___x_59_);
v_job_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_task_69_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_kind_70_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v___x_59_);
v_job_76_ = v_reuseFailAlloc_85_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
lean_ctor_set_uint8(v_job_76_, sizeof(void*)*3, v___x_62_);
v___x_77_ = lean_st_ref_take(v_registeredJobs_74_);
lean_inc_ref(v_job_76_);
v___x_78_ = l_Lake_Job_toOpaque___redArg(v_job_76_);
v___x_79_ = lean_array_push(v___x_77_, v___x_78_);
v___x_80_ = lean_st_ref_put(v_registeredJobs_74_, v___x_79_);
v___x_81_ = l_Lake_Job_renew___redArg(v_job_76_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_81_);
v___x_83_ = v___x_67_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_a_65_);
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
lean_dec_ref(v___x_59_);
return v___x_63_;
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
lean_object* v_toContext_139_; lean_object* v_lakeEnv_140_; lean_object* v_log_141_; uint8_t v_action_142_; uint8_t v_wantsRebuild_143_; uint8_t v_canceled_144_; lean_object* v_trace_145_; lean_object* v_buildTime_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_198_; 
v_toContext_139_ = lean_ctor_get(v___y_136_, 1);
v_lakeEnv_140_ = lean_ctor_get(v_toContext_139_, 0);
v_log_141_ = lean_ctor_get(v___y_137_, 0);
v_action_142_ = lean_ctor_get_uint8(v___y_137_, sizeof(void*)*3);
v_wantsRebuild_143_ = lean_ctor_get_uint8(v___y_137_, sizeof(void*)*3 + 1);
v_canceled_144_ = lean_ctor_get_uint8(v___y_137_, sizeof(void*)*3 + 2);
v_trace_145_ = lean_ctor_get(v___y_137_, 1);
v_buildTime_146_ = lean_ctor_get(v___y_137_, 2);
v_isSharedCheck_198_ = !lean_is_exclusive(v___y_137_);
if (v_isSharedCheck_198_ == 0)
{
v___x_148_ = v___y_137_;
v_isShared_149_ = v_isSharedCheck_198_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_buildTime_146_);
lean_inc(v_trace_145_);
lean_inc(v_log_141_);
lean_dec(v___y_137_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_198_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_lean_150_; lean_object* v___y_152_; uint8_t v___x_188_; 
v_lean_150_ = lean_ctor_get(v_lakeEnv_140_, 1);
v___x_188_ = l_System_Platform_isOSX;
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3));
v___x_190_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4);
v___x_191_ = lean_array_push(v___x_190_, v_staticLib_131_);
v___x_192_ = lean_array_push(v___x_191_, v___x_189_);
v___y_152_ = v___x_192_;
goto v___jp_151_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_193_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5));
v___x_194_ = lean_string_append(v___x_193_, v_staticLib_131_);
lean_dec_ref(v_staticLib_131_);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_mk_empty_array_with_capacity(v___x_195_);
v___x_197_ = lean_array_push(v___x_196_, v___x_194_);
v___y_152_ = v___x_197_;
goto v___jp_151_;
}
v___jp_151_:
{
lean_object* v_leanLibDir_153_; lean_object* v_cc_154_; lean_object* v_ccLinkSharedFlags_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_leanLibDir_153_ = lean_ctor_get(v_lean_150_, 3);
v_cc_154_ = lean_ctor_get(v_lean_150_, 14);
v_ccLinkSharedFlags_155_ = lean_ctor_get(v_lean_150_, 20);
v___x_156_ = l_Array_append___redArg(v___y_152_, v_weakArgs_128_);
v___x_157_ = l_Array_append___redArg(v___x_156_, v_traceArgs_129_);
v___x_158_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1);
lean_inc_ref(v_leanLibDir_153_);
v___x_159_ = lean_array_push(v___x_158_, v_leanLibDir_153_);
v___x_160_ = l_Array_append___redArg(v___x_157_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_161_ = l_Array_append___redArg(v___x_160_, v_ccLinkSharedFlags_155_);
v___x_162_ = lean_box(0);
lean_inc_ref(v_cc_154_);
v___x_163_ = l_Lake_compileSharedLib(v___x_130_, v___x_161_, v_cc_154_, v___x_162_, v_log_141_);
lean_dec_ref(v___x_161_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_175_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_a_165_ = lean_ctor_get(v___x_163_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_175_ == 0)
{
v___x_167_ = v___x_163_;
v_isShared_168_ = v_isSharedCheck_175_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_175_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v_a_165_);
v___x_170_ = v___x_148_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_165_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_trace_145_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_buildTime_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, sizeof(void*)*3, v_action_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, sizeof(void*)*3 + 1, v_wantsRebuild_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_174_, sizeof(void*)*3 + 2, v_canceled_144_);
v___x_170_ = v_reuseFailAlloc_174_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_170_);
v___x_172_ = v___x_167_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_164_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_187_; 
v_a_176_ = lean_ctor_get(v___x_163_, 0);
v_a_177_ = lean_ctor_get(v___x_163_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_187_ == 0)
{
v___x_179_ = v___x_163_;
v_isShared_180_ = v_isSharedCheck_187_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_inc(v_a_176_);
lean_dec(v___x_163_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_187_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v_a_177_);
v___x_182_ = v___x_148_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_177_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_trace_145_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_buildTime_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*3, v_action_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*3 + 1, v_wantsRebuild_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_186_, sizeof(void*)*3 + 2, v_canceled_144_);
v___x_182_ = v_reuseFailAlloc_186_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v___x_182_);
v___x_184_ = v___x_179_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_176_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object* v_weakArgs_199_, lean_object* v_traceArgs_200_, lean_object* v___x_201_, lean_object* v_staticLib_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_buildLeanSharedLibOfStatic___lam__0(v_weakArgs_199_, v_traceArgs_200_, v___x_201_, v_staticLib_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec_ref(v_traceArgs_200_);
lean_dec_ref(v_weakArgs_199_);
return v_res_210_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(lean_object* v_as_211_, size_t v_i_212_, size_t v_stop_213_, uint64_t v_b_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = lean_usize_dec_eq(v_i_212_, v_stop_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v___x_219_; uint64_t v___x_220_; size_t v___x_221_; size_t v___x_222_; 
v___x_216_ = lean_array_uget_borrowed(v_as_211_, v_i_212_);
v___x_217_ = l_Lake_Hash_nil;
v___x_218_ = lean_string_hash(v___x_216_);
v___x_219_ = lean_uint64_mix_hash(v___x_217_, v___x_218_);
v___x_220_ = lean_uint64_mix_hash(v_b_214_, v___x_219_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_i_212_, v___x_221_);
v_i_212_ = v___x_222_;
v_b_214_ = v___x_220_;
goto _start;
}
else
{
return v_b_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(lean_object* v_as_224_, lean_object* v_i_225_, lean_object* v_stop_226_, lean_object* v_b_227_){
_start:
{
size_t v_i_boxed_228_; size_t v_stop_boxed_229_; uint64_t v_b_boxed_230_; uint64_t v_res_231_; lean_object* v_r_232_; 
v_i_boxed_228_ = lean_unbox_usize(v_i_225_);
lean_dec(v_i_225_);
v_stop_boxed_229_ = lean_unbox_usize(v_stop_226_);
lean_dec(v_stop_226_);
v_b_boxed_230_ = lean_unbox_uint64(v_b_227_);
lean_dec_ref(v_b_227_);
v_res_231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_as_224_, v_i_boxed_228_, v_stop_boxed_229_, v_b_boxed_230_);
lean_dec_ref(v_as_224_);
v_r_232_ = lean_box_uint64(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
return v_x_234_;
}
else
{
lean_object* v_head_236_; lean_object* v_tail_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_head_236_ = lean_ctor_get(v_x_235_, 0);
v_tail_237_ = lean_ctor_get(v_x_235_, 1);
v___x_238_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0));
v___x_239_ = lean_string_append(v_x_234_, v___x_238_);
v___x_240_ = lean_string_append(v___x_239_, v_head_236_);
v_x_234_ = v___x_240_;
v_x_235_ = v_tail_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v_x_242_, v_x_243_);
lean_dec(v_x_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_249_; 
v___x_249_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0));
return v___x_249_;
}
else
{
lean_object* v_tail_250_; 
v_tail_250_ = lean_ctor_get(v_x_248_, 1);
if (lean_obj_tag(v_tail_250_) == 0)
{
lean_object* v_head_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_head_251_ = lean_ctor_get(v_x_248_, 0);
v___x_252_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_253_ = lean_string_append(v___x_252_, v_head_251_);
v___x_254_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2));
v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
return v___x_255_;
}
else
{
lean_object* v_head_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint32_t v___x_260_; lean_object* v___x_261_; 
v_head_256_ = lean_ctor_get(v_x_248_, 0);
v___x_257_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_258_ = lean_string_append(v___x_257_, v_head_256_);
v___x_259_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v___x_258_, v_tail_250_);
v___x_260_ = 93;
v___x_261_ = lean_string_push(v___x_259_, v___x_260_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v_x_262_);
lean_dec(v_x_262_);
return v_res_263_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_nat_to_int(v___x_268_);
return v___x_269_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4(void){
_start:
{
uint32_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = 0;
v___x_271_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3);
v___x_272_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set_uint32(v___x_272_, sizeof(void*)*1, v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object* v_traceArgs_273_, lean_object* v_weakArgs_274_, lean_object* v_staticLib_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_log_283_; uint8_t v_action_284_; uint8_t v_wantsRebuild_285_; uint8_t v_canceled_286_; lean_object* v_trace_287_; lean_object* v_buildTime_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_341_; 
v_log_283_ = lean_ctor_get(v___y_281_, 0);
v_action_284_ = lean_ctor_get_uint8(v___y_281_, sizeof(void*)*3);
v_wantsRebuild_285_ = lean_ctor_get_uint8(v___y_281_, sizeof(void*)*3 + 1);
v_canceled_286_ = lean_ctor_get_uint8(v___y_281_, sizeof(void*)*3 + 2);
v_trace_287_ = lean_ctor_get(v___y_281_, 1);
v_buildTime_288_ = lean_ctor_get(v___y_281_, 2);
v_isSharedCheck_341_ = !lean_is_exclusive(v___y_281_);
if (v_isSharedCheck_341_ == 0)
{
v___x_290_ = v___y_281_;
v_isShared_291_ = v_isSharedCheck_341_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_buildTime_288_);
lean_inc(v_trace_287_);
lean_inc(v_log_283_);
lean_dec(v___y_281_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_341_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_leanTrace_292_; lean_object* v___x_293_; uint64_t v___y_295_; uint64_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_leanTrace_292_ = lean_ctor_get(v___y_280_, 2);
lean_inc_ref(v_leanTrace_292_);
v___x_293_ = l_Lake_BuildTrace_mix(v_trace_287_, v_leanTrace_292_);
v___x_334_ = l_Lake_Hash_nil;
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_array_get_size(v_traceArgs_273_);
v___x_337_ = lean_nat_dec_lt(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
v___y_295_ = v___x_334_;
goto v___jp_294_;
}
else
{
size_t v___x_338_; size_t v___x_339_; uint64_t v___x_340_; 
v___x_338_ = ((size_t)0ULL);
v___x_339_ = lean_usize_of_nat(v___x_336_);
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_273_, v___x_338_, v___x_339_, v___x_334_);
v___y_295_ = v___x_340_;
goto v___jp_294_;
}
v___jp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_296_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0));
v___x_297_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1));
lean_inc_ref(v_traceArgs_273_);
v___x_298_ = lean_array_to_list(v_traceArgs_273_);
v___x_299_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v___x_298_);
lean_dec(v___x_298_);
v___x_300_ = lean_string_append(v___x_297_, v___x_299_);
lean_dec_ref(v___x_299_);
v___x_301_ = lean_string_append(v___x_296_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_302_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2));
v___x_303_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4);
v___x_304_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_304_, 0, v___x_301_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
lean_ctor_set_uint64(v___x_304_, sizeof(void*)*3, v___y_295_);
v___x_305_ = l_Lake_BuildTrace_mix(v___x_293_, v___x_304_);
v___x_306_ = l_Lake_platformTrace;
v___x_307_ = l_Lake_BuildTrace_mix(v___x_305_, v___x_306_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v___x_307_);
v___x_309_ = v___x_290_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_log_283_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_buildTime_288_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*3, v_action_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*3 + 1, v_wantsRebuild_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_333_, sizeof(void*)*3 + 2, v_canceled_286_);
v___x_309_ = v_reuseFailAlloc_333_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___f_312_; uint8_t v___x_313_; lean_object* v___x_314_; 
v___x_310_ = l_Lake_sharedLibExt;
lean_inc_ref(v_staticLib_275_);
v___x_311_ = l_System_FilePath_withExtension(v_staticLib_275_, v___x_310_);
lean_inc_ref_n(v___x_311_, 2);
v___f_312_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed), 11, 4);
lean_closure_set(v___f_312_, 0, v_weakArgs_274_);
lean_closure_set(v___f_312_, 1, v_traceArgs_273_);
lean_closure_set(v___f_312_, 2, v___x_311_);
lean_closure_set(v___f_312_, 3, v_staticLib_275_);
v___x_313_ = 0;
v___x_314_ = l_Lake_buildFileUnlessUpToDate_x27(v___x_311_, v___f_312_, v___x_313_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___x_309_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v___x_314_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v___x_314_, 0);
lean_dec(v_unused_323_);
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_311_);
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v___x_311_);
v_a_324_ = lean_ctor_get(v___x_314_, 0);
v_a_325_ = lean_ctor_get(v___x_314_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_314_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_inc(v_a_324_);
lean_dec(v___x_314_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_324_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object* v_traceArgs_342_, lean_object* v_weakArgs_343_, lean_object* v_staticLib_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lake_buildLeanSharedLibOfStatic___lam__1(v_traceArgs_342_, v_weakArgs_343_, v_staticLib_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* v_staticLibJob_353_, lean_object* v_weakArgs_354_, lean_object* v_traceArgs_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; 
v___f_363_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed), 10, 2);
lean_closure_set(v___f_363_, 0, v_traceArgs_355_);
lean_closure_set(v___f_363_, 1, v_weakArgs_354_);
v___x_364_ = l_Lake_instDataKindFilePath;
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = 0;
v___x_367_ = l_Lake_Job_mapM___redArg(v___x_364_, v_staticLibJob_353_, v___f_363_, v___x_365_, v___x_366_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object* v_staticLibJob_368_, lean_object* v_weakArgs_369_, lean_object* v_traceArgs_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lake_buildLeanSharedLibOfStatic(v_staticLibJob_368_, v_weakArgs_369_, v_traceArgs_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec(v_a_373_);
lean_dec(v_a_372_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1));
v___x_383_ = l_Lake_BuildTrace_nil(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object* v___x_384_, lean_object* v_config_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
lean_inc_ref(v___y_386_);
lean_inc_ref(v___y_390_);
lean_inc(v___y_389_);
lean_inc(v___y_388_);
lean_inc(v___y_387_);
v___x_393_ = lean_apply_7(v___y_386_, v___x_384_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, lean_box(0));
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_toLeanConfig_394_; lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_407_; 
v_toLeanConfig_394_ = lean_ctor_get(v_config_385_, 1);
lean_inc_ref(v_toLeanConfig_394_);
lean_dec_ref(v_config_385_);
v_a_395_ = lean_ctor_get(v___x_393_, 0);
v_a_396_ = lean_ctor_get(v___x_393_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_407_ == 0)
{
v___x_398_ = v___x_393_;
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_inc(v_a_395_);
lean_dec(v___x_393_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_moreLinkArgs_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v_moreLinkArgs_400_ = lean_ctor_get(v_toLeanConfig_394_, 8);
lean_inc_ref(v_moreLinkArgs_400_);
lean_dec_ref(v_toLeanConfig_394_);
v___x_401_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0));
v___x_402_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_403_ = l_Lake_buildLeanSharedLibOfStatic(v_a_395_, v_moreLinkArgs_400_, v___x_401_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___x_402_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_403_);
v___x_405_ = v___x_398_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_a_396_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
else
{
lean_dec_ref(v___y_386_);
lean_dec_ref(v_config_385_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object* v___x_408_, lean_object* v_config_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(v___x_408_, v_config_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec(v___y_412_);
lean_dec(v___y_411_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object* v_lib_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_pkg_427_; lean_object* v_name_428_; lean_object* v_keyName_429_; lean_object* v_config_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; uint8_t v___x_443_; lean_object* v___x_444_; 
v_pkg_427_ = lean_ctor_get(v_lib_419_, 0);
v_name_428_ = lean_ctor_get(v_lib_419_, 1);
v_keyName_429_ = lean_ctor_get(v_pkg_427_, 2);
v_config_430_ = lean_ctor_get(v_pkg_427_, 6);
lean_inc_ref(v_config_430_);
v___x_431_ = l_Lake_instDataKindFilePath;
v___x_432_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
lean_inc_n(v_name_428_, 2);
v___x_433_ = l_Lean_Name_str___override(v_name_428_, v___x_432_);
v___x_434_ = 1;
v___x_435_ = l_Lean_Name_toString(v___x_433_, v___x_434_);
v___x_436_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0));
v___x_437_ = lean_string_append(v___x_435_, v___x_436_);
v___x_438_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_keyName_429_);
v___x_439_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_439_, 0, v_keyName_429_);
lean_ctor_set(v___x_439_, 1, v_name_428_);
v___x_440_ = l_Lake_ExternLib_keyword;
v___x_441_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_ctor_set(v___x_441_, 2, v_lib_419_);
lean_ctor_set(v___x_441_, 3, v___x_438_);
v___f_442_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed), 9, 2);
lean_closure_set(v___f_442_, 0, v___x_441_);
lean_closure_set(v___f_442_, 1, v_config_430_);
v___x_443_ = 0;
v___x_444_ = l_Lake_ensureJob___redArg(v___x_431_, v___f_442_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_469_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_a_446_ = lean_ctor_get(v___x_444_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_469_ == 0)
{
v___x_448_ = v___x_444_;
v_isShared_449_ = v_isSharedCheck_469_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_469_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_task_450_; lean_object* v_kind_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_467_; 
v_task_450_ = lean_ctor_get(v_a_445_, 0);
v_kind_451_ = lean_ctor_get(v_a_445_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v_a_445_, 2);
lean_dec(v_unused_468_);
v___x_453_ = v_a_445_;
v_isShared_454_ = v_isSharedCheck_467_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_kind_451_);
lean_inc(v_task_450_);
lean_dec(v_a_445_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_467_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_registeredJobs_455_; lean_object* v_job_457_; 
v_registeredJobs_455_ = lean_ctor_get(v_a_424_, 4);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 2, v___x_437_);
v_job_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_task_450_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_kind_451_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v___x_437_);
v_job_457_ = v_reuseFailAlloc_466_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
lean_ctor_set_uint8(v_job_457_, sizeof(void*)*3, v___x_443_);
v___x_458_ = lean_st_ref_take(v_registeredJobs_455_);
lean_inc_ref(v_job_457_);
v___x_459_ = l_Lake_Job_toOpaque___redArg(v_job_457_);
v___x_460_ = lean_array_push(v___x_458_, v___x_459_);
v___x_461_ = lean_st_ref_put(v_registeredJobs_455_, v___x_460_);
v___x_462_ = l_Lake_Job_renew___redArg(v_job_457_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_462_);
v___x_464_ = v___x_448_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_a_446_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_437_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object* v_lib_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(v_lib_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec(v_a_473_);
lean_dec(v_a_472_);
return v_res_478_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___f_480_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_481_ = 1;
v___x_482_ = l_Lake_instDataKindFilePath;
v___x_483_ = ((lean_object*)(l_Lake_ExternLib_sharedFacetConfig___closed__0));
v___x_484_ = l_Lake_ExternLib_keyword;
v___x_485_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_483_);
lean_ctor_set(v___x_485_, 2, v___x_482_);
lean_ctor_set(v___x_485_, 3, v___f_480_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*4, v___x_481_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*4 + 1, v___x_481_);
return v___x_485_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_obj_once(&l_Lake_ExternLib_sharedFacetConfig___closed__1, &l_Lake_ExternLib_sharedFacetConfig___closed__1_once, _init_l_Lake_ExternLib_sharedFacetConfig___closed__1);
return v___x_486_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_491_ = lean_string_utf8_byte_size(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object* v_sharedLib_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_526_; 
lean_inc_ref(v_sharedLib_495_);
v___x_526_ = l_System_FilePath_fileStem(v_sharedLib_495_);
if (lean_obj_tag(v___x_526_) == 1)
{
lean_object* v_val_527_; uint8_t v___x_528_; 
v_val_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_System_Platform_isWindows;
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_530_ = lean_string_utf8_byte_size(v_val_527_);
v___x_531_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3, &l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_once, _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3);
v___x_532_ = lean_nat_dec_le(v___x_531_, v___x_530_);
if (v___x_532_ == 0)
{
lean_dec(v_val_527_);
goto v___jp_503_;
}
else
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_string_memcmp(v_val_527_, v___x_529_, v___x_533_, v___x_533_, v___x_531_);
if (v___x_534_ == 0)
{
lean_dec(v_val_527_);
goto v___jp_503_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_535_ = lean_unsigned_to_nat(3u);
lean_inc(v_val_527_);
v___x_536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_536_, 0, v_val_527_);
lean_ctor_set(v___x_536_, 1, v___x_533_);
lean_ctor_set(v___x_536_, 2, v___x_530_);
v___x_537_ = l_String_Slice_Pos_nextn(v___x_536_, v___x_533_, v___x_535_);
lean_dec_ref_known(v___x_536_, 3);
v___x_538_ = lean_string_utf8_extract_fast(v_val_527_, v___x_537_, v___x_530_);
lean_dec(v___x_537_);
lean_dec(v_val_527_);
v___x_539_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4));
v___x_540_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_540_, 0, v_sharedLib_495_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
lean_ctor_set(v___x_540_, 3, v___x_539_);
lean_ctor_set_uint8(v___x_540_, sizeof(void*)*4, v___x_528_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___y_501_);
return v___x_541_;
}
}
}
else
{
uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_542_ = 0;
v___x_543_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4));
v___x_544_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_544_, 0, v_sharedLib_495_);
lean_ctor_set(v___x_544_, 1, v_val_527_);
lean_ctor_set(v___x_544_, 2, v___x_543_);
lean_ctor_set(v___x_544_, 3, v___x_543_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*4, v___x_542_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___y_501_);
return v___x_545_;
}
}
else
{
lean_object* v_log_546_; uint8_t v_action_547_; uint8_t v_wantsRebuild_548_; uint8_t v_canceled_549_; lean_object* v_trace_550_; lean_object* v_buildTime_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_567_; 
lean_dec(v___x_526_);
v_log_546_ = lean_ctor_get(v___y_501_, 0);
v_action_547_ = lean_ctor_get_uint8(v___y_501_, sizeof(void*)*3);
v_wantsRebuild_548_ = lean_ctor_get_uint8(v___y_501_, sizeof(void*)*3 + 1);
v_canceled_549_ = lean_ctor_get_uint8(v___y_501_, sizeof(void*)*3 + 2);
v_trace_550_ = lean_ctor_get(v___y_501_, 1);
v_buildTime_551_ = lean_ctor_get(v___y_501_, 2);
v_isSharedCheck_567_ = !lean_is_exclusive(v___y_501_);
if (v_isSharedCheck_567_ == 0)
{
v___x_553_ = v___y_501_;
v_isShared_554_ = v_isSharedCheck_567_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_buildTime_551_);
lean_inc(v_trace_550_);
lean_inc(v_log_546_);
lean_dec(v___y_501_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_567_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_555_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_556_ = lean_string_append(v___x_555_, v_sharedLib_495_);
lean_dec_ref(v_sharedLib_495_);
v___x_557_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5));
v___x_558_ = lean_string_append(v___x_556_, v___x_557_);
v___x_559_ = 3;
v___x_560_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*1, v___x_559_);
v___x_561_ = lean_array_get_size(v_log_546_);
v___x_562_ = lean_array_push(v_log_546_, v___x_560_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_562_);
v___x_564_ = v___x_553_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_trace_550_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_buildTime_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3, v_action_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3 + 1, v_wantsRebuild_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_566_, sizeof(void*)*3 + 2, v_canceled_549_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_561_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
}
v___jp_503_:
{
lean_object* v_log_504_; uint8_t v_action_505_; uint8_t v_wantsRebuild_506_; uint8_t v_canceled_507_; lean_object* v_trace_508_; lean_object* v_buildTime_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_525_; 
v_log_504_ = lean_ctor_get(v___y_501_, 0);
v_action_505_ = lean_ctor_get_uint8(v___y_501_, sizeof(void*)*3);
v_wantsRebuild_506_ = lean_ctor_get_uint8(v___y_501_, sizeof(void*)*3 + 1);
v_canceled_507_ = lean_ctor_get_uint8(v___y_501_, sizeof(void*)*3 + 2);
v_trace_508_ = lean_ctor_get(v___y_501_, 1);
v_buildTime_509_ = lean_ctor_get(v___y_501_, 2);
v_isSharedCheck_525_ = !lean_is_exclusive(v___y_501_);
if (v_isSharedCheck_525_ == 0)
{
v___x_511_ = v___y_501_;
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_buildTime_509_);
lean_inc(v_trace_508_);
lean_inc(v_log_504_);
lean_dec(v___y_501_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_525_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_513_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_514_ = lean_string_append(v___x_513_, v_sharedLib_495_);
lean_dec_ref(v_sharedLib_495_);
v___x_515_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1));
v___x_516_ = lean_string_append(v___x_514_, v___x_515_);
v___x_517_ = 3;
v___x_518_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*1, v___x_517_);
v___x_519_ = lean_array_get_size(v_log_504_);
v___x_520_ = lean_array_push(v_log_504_, v___x_518_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_520_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_trace_508_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_buildTime_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_524_, sizeof(void*)*3, v_action_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_524_, sizeof(void*)*3 + 1, v_wantsRebuild_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_524_, sizeof(void*)*3 + 2, v_canceled_507_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_519_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object* v_sharedLib_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(v_sharedLib_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object* v_sharedLibTarget_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; 
v___f_586_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0));
v___x_587_ = l_Lake_instDataKindDynlib;
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = 0;
v___x_590_ = l_Lake_Job_mapM___redArg(v___x_587_, v_sharedLibTarget_578_, v___f_586_, v___x_588_, v___x_589_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object* v_sharedLibTarget_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_sharedLibTarget_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
lean_dec_ref(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec(v_a_594_);
lean_dec(v_a_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object* v___x_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
lean_inc_ref(v___y_601_);
lean_inc_ref(v___y_605_);
lean_inc(v___y_604_);
lean_inc(v___y_603_);
lean_inc(v___y_602_);
v___x_608_ = lean_apply_7(v___y_601_, v___x_600_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, lean_box(0));
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_619_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_a_610_ = lean_ctor_get(v___x_608_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_619_ == 0)
{
v___x_612_ = v___x_608_;
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_614_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_615_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_a_609_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___x_614_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_615_);
v___x_617_ = v___x_612_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_a_610_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v___y_601_);
v_a_620_ = lean_ctor_get(v___x_608_, 0);
v_a_621_ = lean_ctor_get(v___x_608_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_608_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_inc(v_a_620_);
lean_dec(v___x_608_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object* v___x_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(v___x_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec(v___y_632_);
lean_dec(v___y_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object* v_lib_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_pkg_647_; lean_object* v_name_648_; lean_object* v_keyName_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___f_661_; uint8_t v___x_662_; lean_object* v___x_663_; 
v_pkg_647_ = lean_ctor_get(v_lib_639_, 0);
v_name_648_ = lean_ctor_get(v_lib_639_, 1);
v_keyName_649_ = lean_ctor_get(v_pkg_647_, 2);
v___x_650_ = l_Lake_instDataKindDynlib;
v___x_651_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
lean_inc_n(v_name_648_, 2);
v___x_652_ = l_Lean_Name_str___override(v_name_648_, v___x_651_);
v___x_653_ = 1;
v___x_654_ = l_Lean_Name_toString(v___x_652_, v___x_653_);
v___x_655_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0));
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
v___x_657_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_keyName_649_);
v___x_658_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_658_, 0, v_keyName_649_);
lean_ctor_set(v___x_658_, 1, v_name_648_);
v___x_659_ = l_Lake_ExternLib_keyword;
v___x_660_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
lean_ctor_set(v___x_660_, 2, v_lib_639_);
lean_ctor_set(v___x_660_, 3, v___x_657_);
v___f_661_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed), 8, 1);
lean_closure_set(v___f_661_, 0, v___x_660_);
v___x_662_ = 0;
v___x_663_ = l_Lake_ensureJob___redArg(v___x_650_, v___f_661_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_688_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_a_665_ = lean_ctor_get(v___x_663_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_688_ == 0)
{
v___x_667_ = v___x_663_;
v_isShared_668_ = v_isSharedCheck_688_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_688_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_task_669_; lean_object* v_kind_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_686_; 
v_task_669_ = lean_ctor_get(v_a_664_, 0);
v_kind_670_ = lean_ctor_get(v_a_664_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_a_664_, 2);
lean_dec(v_unused_687_);
v___x_672_ = v_a_664_;
v_isShared_673_ = v_isSharedCheck_686_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_kind_670_);
lean_inc(v_task_669_);
lean_dec(v_a_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_686_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_registeredJobs_674_; lean_object* v_job_676_; 
v_registeredJobs_674_ = lean_ctor_get(v_a_644_, 4);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 2, v___x_656_);
v_job_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_task_669_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_kind_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_656_);
v_job_676_ = v_reuseFailAlloc_685_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
lean_ctor_set_uint8(v_job_676_, sizeof(void*)*3, v___x_662_);
v___x_677_ = lean_st_ref_take(v_registeredJobs_674_);
lean_inc_ref(v_job_676_);
v___x_678_ = l_Lake_Job_toOpaque___redArg(v_job_676_);
v___x_679_ = lean_array_push(v___x_677_, v___x_678_);
v___x_680_ = lean_st_ref_put(v_registeredJobs_674_, v___x_679_);
v___x_681_ = l_Lake_Job_renew___redArg(v_job_676_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_681_);
v___x_683_ = v___x_667_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_a_665_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_656_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object* v_lib_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(v_lib_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec(v_a_692_);
lean_dec(v_a_691_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t v_fmt_698_, lean_object* v_a_699_){
_start:
{
if (v_fmt_698_ == 0)
{
lean_object* v_path_700_; 
v_path_700_ = lean_ctor_get(v_a_699_, 0);
lean_inc_ref(v_path_700_);
return v_path_700_;
}
else
{
lean_object* v_path_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_path_701_ = lean_ctor_get(v_a_699_, 0);
lean_inc_ref(v_path_701_);
v___x_702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_702_, 0, v_path_701_);
v___x_703_ = l_Lean_Json_compress(v___x_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object* v_fmt_704_, lean_object* v_a_705_){
_start:
{
uint8_t v_fmt_boxed_706_; lean_object* v_res_707_; 
v_fmt_boxed_706_ = lean_unbox(v_fmt_704_);
v_res_707_ = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(v_fmt_boxed_706_, v_a_705_);
lean_dec_ref(v_a_705_);
return v_res_707_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___f_710_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__0));
v___x_711_ = 1;
v___x_712_ = l_Lake_instDataKindDynlib;
v___x_713_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__1));
v___x_714_ = l_Lake_ExternLib_keyword;
v___x_715_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_712_);
lean_ctor_set(v___x_715_, 3, v___f_710_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*4, v___x_711_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*4 + 1, v___x_711_);
return v___x_715_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_Lake_ExternLib_dynlibFacetConfig___closed__2, &l_Lake_ExternLib_dynlibFacetConfig___closed__2_once, _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object* v_lib_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_pkg_725_; lean_object* v_name_726_; lean_object* v_keyName_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_pkg_725_ = lean_ctor_get(v_lib_717_, 0);
v_name_726_ = lean_ctor_get(v_lib_717_, 1);
v_keyName_727_ = lean_ctor_get(v_pkg_725_, 2);
v___x_728_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_726_);
lean_inc(v_keyName_727_);
v___x_729_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_729_, 0, v_keyName_727_);
lean_ctor_set(v___x_729_, 1, v_name_726_);
v___x_730_ = l_Lake_ExternLib_keyword;
v___x_731_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_ctor_set(v___x_731_, 2, v_lib_717_);
lean_ctor_set(v___x_731_, 3, v___x_728_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc(v_a_720_);
lean_inc(v_a_719_);
v___x_732_ = lean_apply_7(v_a_718_, v___x_731_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object* v_lib_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(v_lib_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec(v_a_736_);
lean_dec(v_a_735_);
return v_res_741_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_743_; lean_object* v___f_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_743_ = 0;
v___f_744_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_745_ = 1;
v___x_746_ = l_Lake_instDataKindFilePath;
v___x_747_ = ((lean_object*)(l_Lake_ExternLib_defaultFacetConfig___closed__0));
v___x_748_ = l_Lake_ExternLib_keyword;
v___x_749_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
lean_ctor_set(v___x_749_, 2, v___x_746_);
lean_ctor_set(v___x_749_, 3, v___f_744_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*4, v___x_745_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*4 + 1, v___x_743_);
return v___x_749_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_obj_once(&l_Lake_ExternLib_defaultFacetConfig___closed__1, &l_Lake_ExternLib_defaultFacetConfig___closed__1_once, _init_l_Lake_ExternLib_defaultFacetConfig___closed__1);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_751_, lean_object* v_v_752_, lean_object* v_t_753_){
_start:
{
if (lean_obj_tag(v_t_753_) == 0)
{
lean_object* v_size_754_; lean_object* v_k_755_; lean_object* v_v_756_; lean_object* v_l_757_; lean_object* v_r_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_1038_; 
v_size_754_ = lean_ctor_get(v_t_753_, 0);
v_k_755_ = lean_ctor_get(v_t_753_, 1);
v_v_756_ = lean_ctor_get(v_t_753_, 2);
v_l_757_ = lean_ctor_get(v_t_753_, 3);
v_r_758_ = lean_ctor_get(v_t_753_, 4);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_t_753_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_760_ = v_t_753_;
v_isShared_761_ = v_isSharedCheck_1038_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_r_758_);
lean_inc(v_l_757_);
lean_inc(v_v_756_);
lean_inc(v_k_755_);
lean_inc(v_size_754_);
lean_dec(v_t_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_1038_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
uint8_t v___x_762_; 
v___x_762_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_751_, v_k_755_);
switch(v___x_762_)
{
case 0:
{
lean_object* v_impl_763_; lean_object* v___x_764_; 
lean_dec(v_size_754_);
v_impl_763_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_751_, v_v_752_, v_l_757_);
v___x_764_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_758_) == 0)
{
lean_object* v_size_765_; lean_object* v_size_766_; lean_object* v_k_767_; lean_object* v_v_768_; lean_object* v_l_769_; lean_object* v_r_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_size_765_ = lean_ctor_get(v_r_758_, 0);
v_size_766_ = lean_ctor_get(v_impl_763_, 0);
lean_inc(v_size_766_);
v_k_767_ = lean_ctor_get(v_impl_763_, 1);
lean_inc(v_k_767_);
v_v_768_ = lean_ctor_get(v_impl_763_, 2);
lean_inc(v_v_768_);
v_l_769_ = lean_ctor_get(v_impl_763_, 3);
lean_inc(v_l_769_);
v_r_770_ = lean_ctor_get(v_impl_763_, 4);
lean_inc(v_r_770_);
v___x_771_ = lean_unsigned_to_nat(3u);
v___x_772_ = lean_nat_mul(v___x_771_, v_size_765_);
v___x_773_ = lean_nat_dec_lt(v___x_772_, v_size_766_);
lean_dec(v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v_r_770_);
lean_dec(v_l_769_);
lean_dec(v_v_768_);
lean_dec(v_k_767_);
v___x_774_ = lean_nat_add(v___x_764_, v_size_766_);
lean_dec(v_size_766_);
v___x_775_ = lean_nat_add(v___x_774_, v_size_765_);
lean_dec(v___x_774_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 3, v_impl_763_);
lean_ctor_set(v___x_760_, 0, v___x_775_);
v___x_777_ = v___x_760_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_impl_763_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_r_758_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_844_; 
v_isSharedCheck_844_ = !lean_is_exclusive(v_impl_763_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_845_ = lean_ctor_get(v_impl_763_, 4);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_impl_763_, 3);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_impl_763_, 2);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_impl_763_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_impl_763_, 0);
lean_dec(v_unused_849_);
v___x_780_ = v_impl_763_;
v_isShared_781_ = v_isSharedCheck_844_;
goto v_resetjp_779_;
}
else
{
lean_dec(v_impl_763_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_844_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_size_782_; lean_object* v_size_783_; lean_object* v_k_784_; lean_object* v_v_785_; lean_object* v_l_786_; lean_object* v_r_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_size_782_ = lean_ctor_get(v_l_769_, 0);
v_size_783_ = lean_ctor_get(v_r_770_, 0);
v_k_784_ = lean_ctor_get(v_r_770_, 1);
v_v_785_ = lean_ctor_get(v_r_770_, 2);
v_l_786_ = lean_ctor_get(v_r_770_, 3);
v_r_787_ = lean_ctor_get(v_r_770_, 4);
v___x_788_ = lean_unsigned_to_nat(2u);
v___x_789_ = lean_nat_mul(v___x_788_, v_size_782_);
v___x_790_ = lean_nat_dec_lt(v_size_783_, v___x_789_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_819_; 
lean_inc(v_r_787_);
lean_inc(v_l_786_);
lean_inc(v_v_785_);
lean_inc(v_k_784_);
v_isSharedCheck_819_ = !lean_is_exclusive(v_r_770_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; lean_object* v_unused_821_; lean_object* v_unused_822_; lean_object* v_unused_823_; lean_object* v_unused_824_; 
v_unused_820_ = lean_ctor_get(v_r_770_, 4);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_r_770_, 3);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_r_770_, 2);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_r_770_, 1);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_r_770_, 0);
lean_dec(v_unused_824_);
v___x_792_ = v_r_770_;
v_isShared_793_ = v_isSharedCheck_819_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_r_770_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_819_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___x_807_; lean_object* v___y_809_; 
v___x_794_ = lean_nat_add(v___x_764_, v_size_766_);
lean_dec(v_size_766_);
v___x_795_ = lean_nat_add(v___x_794_, v_size_765_);
lean_dec(v___x_794_);
v___x_807_ = lean_nat_add(v___x_764_, v_size_782_);
if (lean_obj_tag(v_l_786_) == 0)
{
lean_object* v_size_817_; 
v_size_817_ = lean_ctor_get(v_l_786_, 0);
lean_inc(v_size_817_);
v___y_809_ = v_size_817_;
goto v___jp_808_;
}
else
{
lean_object* v___x_818_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v___y_809_ = v___x_818_;
goto v___jp_808_;
}
v___jp_796_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_nat_add(v___y_797_, v___y_799_);
lean_dec(v___y_799_);
lean_dec(v___y_797_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v_r_758_);
lean_ctor_set(v___x_792_, 3, v_r_787_);
lean_ctor_set(v___x_792_, 2, v_v_756_);
lean_ctor_set(v___x_792_, 1, v_k_755_);
lean_ctor_set(v___x_792_, 0, v___x_800_);
v___x_802_ = v___x_792_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_r_787_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_r_758_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v___x_802_);
lean_ctor_set(v___x_780_, 3, v___y_798_);
lean_ctor_set(v___x_780_, 2, v_v_785_);
lean_ctor_set(v___x_780_, 1, v_k_784_);
lean_ctor_set(v___x_780_, 0, v___x_795_);
v___x_804_ = v___x_780_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_784_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_785_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v___y_798_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
v___jp_808_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_nat_add(v___x_807_, v___y_809_);
lean_dec(v___y_809_);
lean_dec(v___x_807_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_l_786_);
lean_ctor_set(v___x_760_, 3, v_l_769_);
lean_ctor_set(v___x_760_, 2, v_v_768_);
lean_ctor_set(v___x_760_, 1, v_k_767_);
lean_ctor_set(v___x_760_, 0, v___x_810_);
v___x_812_ = v___x_760_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_l_769_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_l_786_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; 
v___x_813_ = lean_nat_add(v___x_764_, v_size_765_);
if (lean_obj_tag(v_r_787_) == 0)
{
lean_object* v_size_814_; 
v_size_814_ = lean_ctor_get(v_r_787_, 0);
lean_inc(v_size_814_);
v___y_797_ = v___x_813_;
v___y_798_ = v___x_812_;
v___y_799_ = v_size_814_;
goto v___jp_796_;
}
else
{
lean_object* v___x_815_; 
v___x_815_ = lean_unsigned_to_nat(0u);
v___y_797_ = v___x_813_;
v___y_798_ = v___x_812_;
v___y_799_ = v___x_815_;
goto v___jp_796_;
}
}
}
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_del_object(v___x_760_);
v___x_825_ = lean_nat_add(v___x_764_, v_size_766_);
lean_dec(v_size_766_);
v___x_826_ = lean_nat_add(v___x_825_, v_size_765_);
lean_dec(v___x_825_);
v___x_827_ = lean_nat_add(v___x_764_, v_size_765_);
v___x_828_ = lean_nat_add(v___x_827_, v_size_783_);
lean_dec(v___x_827_);
lean_inc_ref(v_r_758_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v_r_758_);
lean_ctor_set(v___x_780_, 3, v_r_770_);
lean_ctor_set(v___x_780_, 2, v_v_756_);
lean_ctor_set(v___x_780_, 1, v_k_755_);
lean_ctor_set(v___x_780_, 0, v___x_828_);
v___x_830_ = v___x_780_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_r_770_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_r_758_);
v___x_830_ = v_reuseFailAlloc_843_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
v_isSharedCheck_837_ = !lean_is_exclusive(v_r_758_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_838_ = lean_ctor_get(v_r_758_, 4);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_r_758_, 3);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_r_758_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_r_758_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_r_758_, 0);
lean_dec(v_unused_842_);
v___x_832_ = v_r_758_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_dec(v_r_758_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 4, v___x_830_);
lean_ctor_set(v___x_832_, 3, v_l_769_);
lean_ctor_set(v___x_832_, 2, v_v_768_);
lean_ctor_set(v___x_832_, 1, v_k_767_);
lean_ctor_set(v___x_832_, 0, v___x_826_);
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_l_769_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v___x_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_850_; 
v_l_850_ = lean_ctor_get(v_impl_763_, 3);
lean_inc(v_l_850_);
if (lean_obj_tag(v_l_850_) == 0)
{
lean_object* v_r_851_; lean_object* v_k_852_; lean_object* v_v_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_864_; 
v_r_851_ = lean_ctor_get(v_impl_763_, 4);
v_k_852_ = lean_ctor_get(v_impl_763_, 1);
v_v_853_ = lean_ctor_get(v_impl_763_, 2);
v_isSharedCheck_864_ = !lean_is_exclusive(v_impl_763_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; 
v_unused_865_ = lean_ctor_get(v_impl_763_, 3);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_impl_763_, 0);
lean_dec(v_unused_866_);
v___x_855_ = v_impl_763_;
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_r_851_);
lean_inc(v_v_853_);
lean_inc(v_k_852_);
lean_dec(v_impl_763_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_864_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_851_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 3, v_r_851_);
lean_ctor_set(v___x_855_, 2, v_v_756_);
lean_ctor_set(v___x_855_, 1, v_k_755_);
lean_ctor_set(v___x_855_, 0, v___x_764_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v_r_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v_r_851_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v___x_859_);
lean_ctor_set(v___x_760_, 3, v_l_850_);
lean_ctor_set(v___x_760_, 2, v_v_853_);
lean_ctor_set(v___x_760_, 1, v_k_852_);
lean_ctor_set(v___x_760_, 0, v___x_857_);
v___x_861_ = v___x_760_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_k_852_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_v_853_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_l_850_);
lean_ctor_set(v_reuseFailAlloc_862_, 4, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_r_867_; 
v_r_867_ = lean_ctor_get(v_impl_763_, 4);
lean_inc(v_r_867_);
if (lean_obj_tag(v_r_867_) == 0)
{
lean_object* v_k_868_; lean_object* v_v_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_892_; 
v_k_868_ = lean_ctor_get(v_impl_763_, 1);
v_v_869_ = lean_ctor_get(v_impl_763_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_impl_763_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; lean_object* v_unused_894_; lean_object* v_unused_895_; 
v_unused_893_ = lean_ctor_get(v_impl_763_, 4);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_impl_763_, 3);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_impl_763_, 0);
lean_dec(v_unused_895_);
v___x_871_ = v_impl_763_;
v_isShared_872_ = v_isSharedCheck_892_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_v_869_);
lean_inc(v_k_868_);
lean_dec(v_impl_763_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_892_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_k_873_; lean_object* v_v_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_888_; 
v_k_873_ = lean_ctor_get(v_r_867_, 1);
v_v_874_ = lean_ctor_get(v_r_867_, 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_r_867_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; lean_object* v_unused_891_; 
v_unused_889_ = lean_ctor_get(v_r_867_, 4);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_r_867_, 3);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_r_867_, 0);
lean_dec(v_unused_891_);
v___x_876_ = v_r_867_;
v_isShared_877_ = v_isSharedCheck_888_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_v_874_);
lean_inc(v_k_873_);
lean_dec(v_r_867_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_888_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_unsigned_to_nat(3u);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 4, v_l_850_);
lean_ctor_set(v___x_876_, 3, v_l_850_);
lean_ctor_set(v___x_876_, 2, v_v_869_);
lean_ctor_set(v___x_876_, 1, v_k_868_);
lean_ctor_set(v___x_876_, 0, v___x_764_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_868_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_869_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v_l_850_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v_l_850_);
v___x_880_ = v_reuseFailAlloc_887_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 4, v_l_850_);
lean_ctor_set(v___x_871_, 2, v_v_756_);
lean_ctor_set(v___x_871_, 1, v_k_755_);
lean_ctor_set(v___x_871_, 0, v___x_764_);
v___x_882_ = v___x_871_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_l_850_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_l_850_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v___x_882_);
lean_ctor_set(v___x_760_, 3, v___x_880_);
lean_ctor_set(v___x_760_, 2, v_v_874_);
lean_ctor_set(v___x_760_, 1, v_k_873_);
lean_ctor_set(v___x_760_, 0, v___x_878_);
v___x_884_ = v___x_760_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_k_873_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_v_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v___x_882_);
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
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(2u);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_r_867_);
lean_ctor_set(v___x_760_, 3, v_impl_763_);
lean_ctor_set(v___x_760_, 0, v___x_896_);
v___x_898_ = v___x_760_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_impl_763_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_r_867_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
case 1:
{
lean_object* v___x_901_; 
lean_dec(v_v_756_);
lean_dec(v_k_755_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v_v_752_);
lean_ctor_set(v___x_760_, 1, v_k_751_);
v___x_901_ = v___x_760_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_size_754_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_l_757_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_r_758_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
default: 
{
lean_object* v_impl_903_; lean_object* v___x_904_; 
lean_dec(v_size_754_);
v_impl_903_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_751_, v_v_752_, v_r_758_);
v___x_904_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_757_) == 0)
{
lean_object* v_size_905_; lean_object* v_size_906_; lean_object* v_k_907_; lean_object* v_v_908_; lean_object* v_l_909_; lean_object* v_r_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_size_905_ = lean_ctor_get(v_l_757_, 0);
v_size_906_ = lean_ctor_get(v_impl_903_, 0);
lean_inc(v_size_906_);
v_k_907_ = lean_ctor_get(v_impl_903_, 1);
lean_inc(v_k_907_);
v_v_908_ = lean_ctor_get(v_impl_903_, 2);
lean_inc(v_v_908_);
v_l_909_ = lean_ctor_get(v_impl_903_, 3);
lean_inc(v_l_909_);
v_r_910_ = lean_ctor_get(v_impl_903_, 4);
lean_inc(v_r_910_);
v___x_911_ = lean_unsigned_to_nat(3u);
v___x_912_ = lean_nat_mul(v___x_911_, v_size_905_);
v___x_913_ = lean_nat_dec_lt(v___x_912_, v_size_906_);
lean_dec(v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
lean_dec(v_r_910_);
lean_dec(v_l_909_);
lean_dec(v_v_908_);
lean_dec(v_k_907_);
v___x_914_ = lean_nat_add(v___x_904_, v_size_905_);
v___x_915_ = lean_nat_add(v___x_914_, v_size_906_);
lean_dec(v_size_906_);
lean_dec(v___x_914_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_impl_903_);
lean_ctor_set(v___x_760_, 0, v___x_915_);
v___x_917_ = v___x_760_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_l_757_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_impl_903_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
else
{
lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_982_; 
v_isSharedCheck_982_ = !lean_is_exclusive(v_impl_903_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_983_ = lean_ctor_get(v_impl_903_, 4);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_impl_903_, 3);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_impl_903_, 2);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_impl_903_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_impl_903_, 0);
lean_dec(v_unused_987_);
v___x_920_ = v_impl_903_;
v_isShared_921_ = v_isSharedCheck_982_;
goto v_resetjp_919_;
}
else
{
lean_dec(v_impl_903_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_982_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_size_922_; lean_object* v_k_923_; lean_object* v_v_924_; lean_object* v_l_925_; lean_object* v_r_926_; lean_object* v_size_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_size_922_ = lean_ctor_get(v_l_909_, 0);
v_k_923_ = lean_ctor_get(v_l_909_, 1);
v_v_924_ = lean_ctor_get(v_l_909_, 2);
v_l_925_ = lean_ctor_get(v_l_909_, 3);
v_r_926_ = lean_ctor_get(v_l_909_, 4);
v_size_927_ = lean_ctor_get(v_r_910_, 0);
v___x_928_ = lean_unsigned_to_nat(2u);
v___x_929_ = lean_nat_mul(v___x_928_, v_size_927_);
v___x_930_ = lean_nat_dec_lt(v_size_922_, v___x_929_);
lean_dec(v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_958_; 
lean_inc(v_r_926_);
lean_inc(v_l_925_);
lean_inc(v_v_924_);
lean_inc(v_k_923_);
v_isSharedCheck_958_ = !lean_is_exclusive(v_l_909_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; 
v_unused_959_ = lean_ctor_get(v_l_909_, 4);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_l_909_, 3);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_l_909_, 2);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_l_909_, 1);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_909_, 0);
lean_dec(v_unused_963_);
v___x_932_ = v_l_909_;
v_isShared_933_ = v_isSharedCheck_958_;
goto v_resetjp_931_;
}
else
{
lean_dec(v_l_909_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_958_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_948_; 
v___x_934_ = lean_nat_add(v___x_904_, v_size_905_);
v___x_935_ = lean_nat_add(v___x_934_, v_size_906_);
lean_dec(v_size_906_);
if (lean_obj_tag(v_l_925_) == 0)
{
lean_object* v_size_956_; 
v_size_956_ = lean_ctor_get(v_l_925_, 0);
lean_inc(v_size_956_);
v___y_948_ = v_size_956_;
goto v___jp_947_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___y_948_ = v___x_957_;
goto v___jp_947_;
}
v___jp_936_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = lean_nat_add(v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 4, v_r_910_);
lean_ctor_set(v___x_932_, 3, v_r_926_);
lean_ctor_set(v___x_932_, 2, v_v_908_);
lean_ctor_set(v___x_932_, 1, v_k_907_);
lean_ctor_set(v___x_932_, 0, v___x_940_);
v___x_942_ = v___x_932_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_k_907_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_v_908_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_r_926_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_r_910_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 4, v___x_942_);
lean_ctor_set(v___x_920_, 3, v___y_937_);
lean_ctor_set(v___x_920_, 2, v_v_924_);
lean_ctor_set(v___x_920_, 1, v_k_923_);
lean_ctor_set(v___x_920_, 0, v___x_935_);
v___x_944_ = v___x_920_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_k_923_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_v_924_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v___y_937_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
v___jp_947_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_nat_add(v___x_934_, v___y_948_);
lean_dec(v___y_948_);
lean_dec(v___x_934_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_l_925_);
lean_ctor_set(v___x_760_, 0, v___x_949_);
v___x_951_ = v___x_760_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_l_757_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_l_925_);
v___x_951_ = v_reuseFailAlloc_955_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_nat_add(v___x_904_, v_size_927_);
if (lean_obj_tag(v_r_926_) == 0)
{
lean_object* v_size_953_; 
v_size_953_ = lean_ctor_get(v_r_926_, 0);
lean_inc(v_size_953_);
v___y_937_ = v___x_951_;
v___y_938_ = v___x_952_;
v___y_939_ = v_size_953_;
goto v___jp_936_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___y_937_ = v___x_951_;
v___y_938_ = v___x_952_;
v___y_939_ = v___x_954_;
goto v___jp_936_;
}
}
}
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
lean_del_object(v___x_760_);
v___x_964_ = lean_nat_add(v___x_904_, v_size_905_);
v___x_965_ = lean_nat_add(v___x_964_, v_size_906_);
lean_dec(v_size_906_);
v___x_966_ = lean_nat_add(v___x_964_, v_size_922_);
lean_dec(v___x_964_);
lean_inc_ref(v_l_757_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 4, v_l_909_);
lean_ctor_set(v___x_920_, 3, v_l_757_);
lean_ctor_set(v___x_920_, 2, v_v_756_);
lean_ctor_set(v___x_920_, 1, v_k_755_);
lean_ctor_set(v___x_920_, 0, v___x_966_);
v___x_968_ = v___x_920_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_l_757_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_l_909_);
v___x_968_ = v_reuseFailAlloc_981_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_isSharedCheck_975_ = !lean_is_exclusive(v_l_757_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; lean_object* v_unused_977_; lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; 
v_unused_976_ = lean_ctor_get(v_l_757_, 4);
lean_dec(v_unused_976_);
v_unused_977_ = lean_ctor_get(v_l_757_, 3);
lean_dec(v_unused_977_);
v_unused_978_ = lean_ctor_get(v_l_757_, 2);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_l_757_, 1);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_757_, 0);
lean_dec(v_unused_980_);
v___x_970_ = v_l_757_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_dec(v_l_757_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 4, v_r_910_);
lean_ctor_set(v___x_970_, 3, v___x_968_);
lean_ctor_set(v___x_970_, 2, v_v_908_);
lean_ctor_set(v___x_970_, 1, v_k_907_);
lean_ctor_set(v___x_970_, 0, v___x_965_);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_k_907_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_v_908_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_r_910_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_988_; 
v_l_988_ = lean_ctor_get(v_impl_903_, 3);
lean_inc(v_l_988_);
if (lean_obj_tag(v_l_988_) == 0)
{
lean_object* v_r_989_; lean_object* v_k_990_; lean_object* v_v_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1014_; 
v_r_989_ = lean_ctor_get(v_impl_903_, 4);
v_k_990_ = lean_ctor_get(v_impl_903_, 1);
v_v_991_ = lean_ctor_get(v_impl_903_, 2);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_impl_903_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; lean_object* v_unused_1016_; 
v_unused_1015_ = lean_ctor_get(v_impl_903_, 3);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_impl_903_, 0);
lean_dec(v_unused_1016_);
v___x_993_ = v_impl_903_;
v_isShared_994_ = v_isSharedCheck_1014_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_r_989_);
lean_inc(v_v_991_);
lean_inc(v_k_990_);
lean_dec(v_impl_903_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1014_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_k_995_; lean_object* v_v_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1010_; 
v_k_995_ = lean_ctor_get(v_l_988_, 1);
v_v_996_ = lean_ctor_get(v_l_988_, 2);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_l_988_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; lean_object* v_unused_1012_; lean_object* v_unused_1013_; 
v_unused_1011_ = lean_ctor_get(v_l_988_, 4);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_l_988_, 3);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_l_988_, 0);
lean_dec(v_unused_1013_);
v___x_998_ = v_l_988_;
v_isShared_999_ = v_isSharedCheck_1010_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_v_996_);
lean_inc(v_k_995_);
lean_dec(v_l_988_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1010_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_989_, 2);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 4, v_r_989_);
lean_ctor_set(v___x_998_, 3, v_r_989_);
lean_ctor_set(v___x_998_, 2, v_v_756_);
lean_ctor_set(v___x_998_, 1, v_k_755_);
lean_ctor_set(v___x_998_, 0, v___x_904_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_r_989_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_r_989_);
v___x_1002_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
lean_inc(v_r_989_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 3, v_r_989_);
lean_ctor_set(v___x_993_, 0, v___x_904_);
v___x_1004_ = v___x_993_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_r_989_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_r_989_);
v___x_1004_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v___x_1004_);
lean_ctor_set(v___x_760_, 3, v___x_1002_);
lean_ctor_set(v___x_760_, 2, v_v_996_);
lean_ctor_set(v___x_760_, 1, v_k_995_);
lean_ctor_set(v___x_760_, 0, v___x_1000_);
v___x_1006_ = v___x_760_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_k_995_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_v_996_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v___x_1004_);
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
}
}
else
{
lean_object* v_r_1017_; 
v_r_1017_ = lean_ctor_get(v_impl_903_, 4);
lean_inc(v_r_1017_);
if (lean_obj_tag(v_r_1017_) == 0)
{
lean_object* v_k_1018_; lean_object* v_v_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1030_; 
v_k_1018_ = lean_ctor_get(v_impl_903_, 1);
v_v_1019_ = lean_ctor_get(v_impl_903_, 2);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_impl_903_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; lean_object* v_unused_1032_; lean_object* v_unused_1033_; 
v_unused_1031_ = lean_ctor_get(v_impl_903_, 4);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_impl_903_, 3);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_impl_903_, 0);
lean_dec(v_unused_1033_);
v___x_1021_ = v_impl_903_;
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_v_1019_);
lean_inc(v_k_1018_);
lean_dec(v_impl_903_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1030_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = lean_unsigned_to_nat(3u);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 4, v_l_988_);
lean_ctor_set(v___x_1021_, 2, v_v_756_);
lean_ctor_set(v___x_1021_, 1, v_k_755_);
lean_ctor_set(v___x_1021_, 0, v___x_904_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_l_988_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_l_988_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_r_1017_);
lean_ctor_set(v___x_760_, 3, v___x_1025_);
lean_ctor_set(v___x_760_, 2, v_v_1019_);
lean_ctor_set(v___x_760_, 1, v_k_1018_);
lean_ctor_set(v___x_760_, 0, v___x_1023_);
v___x_1027_ = v___x_760_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_k_1018_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_v_1019_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_r_1017_);
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
else
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = lean_unsigned_to_nat(2u);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 4, v_impl_903_);
lean_ctor_set(v___x_760_, 3, v_r_1017_);
lean_ctor_set(v___x_760_, 0, v___x_1034_);
v___x_1036_ = v___x_760_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_k_755_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_v_756_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_r_1017_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_impl_903_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
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
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_k_751_);
lean_ctor_set(v___x_1040_, 2, v_v_752_);
lean_ctor_set(v___x_1040_, 3, v_t_753_);
lean_ctor_set(v___x_1040_, 4, v_t_753_);
return v___x_1040_;
}
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = lean_box(1);
v___x_1042_ = l_Lake_ExternLib_defaultFacetConfig;
v___x_1043_ = l_Lake_ExternLib_defaultFacet;
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1043_, v___x_1042_, v___x_1041_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__0, &l_Lake_ExternLib_initFacetConfigs___closed__0_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__0);
v___x_1046_ = l_Lake_ExternLib_staticFacetConfig;
v___x_1047_ = l_Lake_ExternLib_staticFacet;
v___x_1048_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1047_, v___x_1046_, v___x_1045_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__1, &l_Lake_ExternLib_initFacetConfigs___closed__1_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__1);
v___x_1050_ = l_Lake_ExternLib_sharedFacetConfig;
v___x_1051_ = l_Lake_ExternLib_sharedFacet;
v___x_1052_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1051_, v___x_1050_, v___x_1049_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1053_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__2, &l_Lake_ExternLib_initFacetConfigs___closed__2_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__2);
v___x_1054_ = l_Lake_ExternLib_dynlibFacetConfig;
v___x_1055_ = l_Lake_ExternLib_dynlibFacet;
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1055_, v___x_1054_, v___x_1053_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__3, &l_Lake_ExternLib_initFacetConfigs___closed__3_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__3);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_1058_, lean_object* v_k_1059_, lean_object* v_v_1060_, lean_object* v_t_1061_, lean_object* v_hl_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_1059_, v_v_1060_, v_t_1061_);
return v___x_1063_;
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
