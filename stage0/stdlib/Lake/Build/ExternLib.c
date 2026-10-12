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
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static const lean_array_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3_value;
static const lean_string_object l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` has no file name"};
static const lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_value;
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
lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(lean_object* v___x_1_, lean_object* v_config_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
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
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v_config_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_30_;
v_res_30_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(v___x_1_, v_config_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed(lean_object* v___x_31_, lean_object* v_config_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0(v___x_31_, v_config_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec(v___y_35_);
lean_dec(v___y_34_);
return v_res_40_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(lean_object* v_lib_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_pkg_51_; lean_object* v_name_52_; lean_object* v_config_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; uint8_t v___x_63_; lean_object* v___x_64_; 
v_pkg_51_ = lean_ctor_get(v_lib_43_, 0);
lean_inc_ref(v_pkg_51_);
v_name_52_ = lean_ctor_get(v_lib_43_, 1);
lean_inc(v_name_52_);
v_config_53_ = lean_ctor_get(v_lib_43_, 2);
lean_inc(v_config_53_);
lean_dec_ref(v_lib_43_);
v___x_54_ = l_Lake_instDataKindFilePath;
v___x_55_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_56_ = l_Lean_Name_str___override(v_name_52_, v___x_55_);
v___x_57_ = 1;
lean_inc(v___x_56_);
v___x_58_ = l_Lean_Name_toString(v___x_56_, v___x_57_);
v___x_59_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__1));
v___x_60_ = lean_string_append(v___x_58_, v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_pkg_51_);
lean_ctor_set(v___x_61_, 1, v___x_56_);
v___f_62_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___lam__0___boxed), 9, 2);
lean_closure_set(v___f_62_, 0, v___x_61_);
lean_closure_set(v___f_62_, 1, v_config_53_);
v___x_63_ = 0;
v___x_64_ = l_Lake_ensureJob___redArg(v___x_54_, v___f_62_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_89_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_a_66_ = lean_ctor_get(v___x_64_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_89_ == 0)
{
v___x_68_ = v___x_64_;
v_isShared_69_ = v_isSharedCheck_89_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_89_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_task_70_; lean_object* v_kind_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_87_; 
v_task_70_ = lean_ctor_get(v_a_65_, 0);
v_kind_71_ = lean_ctor_get(v_a_65_, 1);
v_isSharedCheck_87_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v_a_65_, 2);
lean_dec(v_unused_88_);
v___x_73_ = v_a_65_;
v_isShared_74_ = v_isSharedCheck_87_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_kind_71_);
lean_inc(v_task_70_);
lean_dec(v_a_65_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_87_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_registeredJobs_75_; lean_object* v_job_77_; 
v_registeredJobs_75_ = lean_ctor_get(v_a_48_, 4);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 2, v___x_60_);
v_job_77_ = v___x_73_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_task_70_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_kind_71_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v___x_60_);
v_job_77_ = v_reuseFailAlloc_86_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
lean_ctor_set_uint8(v_job_77_, sizeof(void*)*3, v___x_63_);
v___x_78_ = lean_st_ref_take(v_registeredJobs_75_);
lean_inc_ref(v_job_77_);
v___x_79_ = l_Lake_Job_toOpaque___redArg(v_job_77_);
v___x_80_ = lean_array_push(v___x_78_, v___x_79_);
v___x_81_ = lean_st_ref_put(v_registeredJobs_75_, v___x_80_);
v___x_82_ = l_Lake_Job_renew___redArg(v_job_77_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_82_);
v___x_84_ = v___x_68_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_a_66_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_60_);
return v___x_64_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic_0interp(lean_interpreter_value* stack)
{
lean_object* v_lib_43_ = stack[0].m_obj;
lean_object* v_a_44_ = stack[1].m_obj;
lean_object* v_a_45_ = stack[2].m_obj;
lean_object* v_a_46_ = stack[3].m_obj;
lean_object* v_a_47_ = stack[4].m_obj;
lean_object* v_a_48_ = stack[5].m_obj;
lean_object* v_a_49_ = stack[6].m_obj;
lean_object* v_res_90_;
v_res_90_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(v_lib_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed(lean_object* v_lib_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(v_lib_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec(v_a_94_);
lean_dec(v_a_93_);
return v_res_99_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(uint8_t v_fmt_100_, lean_object* v_a_101_){
_start:
{
if (v_fmt_100_ == 0)
{
return v_a_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = l_Lake_mkRelPathString(v_a_101_);
v___x_103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
v___x_104_ = l_Lean_Json_compress(v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_100_ = stack[0].m_num;
lean_object* v_a_101_ = stack[1].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(v_fmt_100_, v_a_101_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0___boxed(lean_object* v_fmt_106_, lean_object* v_a_107_){
_start:
{
uint8_t v_fmt_boxed_108_; lean_object* v_res_109_; 
v_fmt_boxed_108_ = lean_unbox(v_fmt_106_);
v_res_109_ = l_Lake_formatQuery___at___00Lake_ExternLib_staticFacetConfig_spec__0(v_fmt_boxed_108_, v_a_107_);
return v_res_109_;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___f_112_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_113_ = 1;
v___x_114_ = l_Lake_instDataKindFilePath;
v___x_115_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__1));
v___x_116_ = l_Lake_ExternLib_keyword;
v___x_117_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
lean_ctor_set(v___x_117_, 3, v___f_112_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*4, v___x_113_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*4 + 1, v___x_113_);
return v___x_117_;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lake_ExternLib_staticFacetConfig___closed__2, &l_Lake_ExternLib_staticFacetConfig___closed__2_once, _init_l_Lake_ExternLib_staticFacetConfig___closed__2);
return v___x_118_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__0));
v___x_121_ = lean_unsigned_to_nat(2u);
v___x_122_ = lean_mk_empty_array_with_capacity(v___x_121_);
v___x_123_ = lean_array_push(v___x_122_, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__2));
v___x_127_ = lean_unsigned_to_nat(3u);
v___x_128_ = lean_mk_empty_array_with_capacity(v___x_127_);
v___x_129_ = lean_array_push(v___x_128_, v___x_126_);
return v___x_129_;
}
}
lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0(lean_object* v_weakArgs_131_, lean_object* v_traceArgs_132_, lean_object* v___x_133_, lean_object* v_staticLib_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_toContext_142_; lean_object* v_lakeEnv_143_; lean_object* v_log_144_; uint8_t v_action_145_; uint8_t v_wantsRebuild_146_; uint8_t v_canceled_147_; lean_object* v_trace_148_; lean_object* v_buildTime_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_201_; 
v_toContext_142_ = lean_ctor_get(v___y_139_, 1);
v_lakeEnv_143_ = lean_ctor_get(v_toContext_142_, 0);
v_log_144_ = lean_ctor_get(v___y_140_, 0);
v_action_145_ = lean_ctor_get_uint8(v___y_140_, sizeof(void*)*3);
v_wantsRebuild_146_ = lean_ctor_get_uint8(v___y_140_, sizeof(void*)*3 + 1);
v_canceled_147_ = lean_ctor_get_uint8(v___y_140_, sizeof(void*)*3 + 2);
v_trace_148_ = lean_ctor_get(v___y_140_, 1);
v_buildTime_149_ = lean_ctor_get(v___y_140_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v___y_140_);
if (v_isSharedCheck_201_ == 0)
{
v___x_151_ = v___y_140_;
v_isShared_152_ = v_isSharedCheck_201_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_buildTime_149_);
lean_inc(v_trace_148_);
lean_inc(v_log_144_);
lean_dec(v___y_140_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_201_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v_lean_153_; lean_object* v___y_155_; uint8_t v___x_191_; 
v_lean_153_ = lean_ctor_get(v_lakeEnv_143_, 1);
v___x_191_ = l_System_Platform_isOSX;
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3));
v___x_193_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4);
v___x_194_ = lean_array_push(v___x_193_, v_staticLib_134_);
v___x_195_ = lean_array_push(v___x_194_, v___x_192_);
v___y_155_ = v___x_195_;
goto v___jp_154_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5));
v___x_197_ = lean_string_append(v___x_196_, v_staticLib_134_);
lean_dec_ref(v_staticLib_134_);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_mk_empty_array_with_capacity(v___x_198_);
v___x_200_ = lean_array_push(v___x_199_, v___x_197_);
v___y_155_ = v___x_200_;
goto v___jp_154_;
}
v___jp_154_:
{
lean_object* v_leanLibDir_156_; lean_object* v_cc_157_; lean_object* v_ccLinkSharedFlags_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_leanLibDir_156_ = lean_ctor_get(v_lean_153_, 3);
v_cc_157_ = lean_ctor_get(v_lean_153_, 14);
v_ccLinkSharedFlags_158_ = lean_ctor_get(v_lean_153_, 20);
v___x_159_ = l_Array_append___redArg(v___y_155_, v_weakArgs_131_);
v___x_160_ = l_Array_append___redArg(v___x_159_, v_traceArgs_132_);
v___x_161_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1);
lean_inc_ref(v_leanLibDir_156_);
v___x_162_ = lean_array_push(v___x_161_, v_leanLibDir_156_);
v___x_163_ = l_Array_append___redArg(v___x_160_, v___x_162_);
lean_dec_ref(v___x_162_);
v___x_164_ = l_Array_append___redArg(v___x_163_, v_ccLinkSharedFlags_158_);
v___x_165_ = lean_box(0);
lean_inc_ref(v_cc_157_);
v___x_166_ = l_Lake_compileSharedLib(v___x_133_, v___x_164_, v_cc_157_, v___x_165_, v_log_144_);
lean_dec_ref(v___x_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_178_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_a_168_ = lean_ctor_get(v___x_166_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_178_ == 0)
{
v___x_170_ = v___x_166_;
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v_a_168_);
v___x_173_ = v___x_151_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_168_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_trace_148_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_buildTime_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_177_, sizeof(void*)*3, v_action_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_177_, sizeof(void*)*3 + 1, v_wantsRebuild_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_177_, sizeof(void*)*3 + 2, v_canceled_147_);
v___x_173_ = v_reuseFailAlloc_177_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_173_);
v___x_175_ = v___x_170_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_167_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_190_; 
v_a_179_ = lean_ctor_get(v___x_166_, 0);
v_a_180_ = lean_ctor_get(v___x_166_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_190_ == 0)
{
v___x_182_ = v___x_166_;
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_inc(v_a_179_);
lean_dec(v___x_166_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v_a_180_);
v___x_185_ = v___x_151_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_180_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_trace_148_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v_buildTime_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_189_, sizeof(void*)*3, v_action_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_189_, sizeof(void*)*3 + 1, v_wantsRebuild_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_189_, sizeof(void*)*3 + 2, v_canceled_147_);
v___x_185_ = v_reuseFailAlloc_189_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_187_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_179_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_buildLeanSharedLibOfStatic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_weakArgs_131_ = stack[0].m_obj;
lean_object* v_traceArgs_132_ = stack[1].m_obj;
lean_object* v___x_133_ = stack[2].m_obj;
lean_object* v_staticLib_134_ = stack[3].m_obj;
lean_object* v___y_135_ = stack[4].m_obj;
lean_object* v___y_136_ = stack[5].m_obj;
lean_object* v___y_137_ = stack[6].m_obj;
lean_object* v___y_138_ = stack[7].m_obj;
lean_object* v___y_139_ = stack[8].m_obj;
lean_object* v___y_140_ = stack[9].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lake_buildLeanSharedLibOfStatic___lam__0(v_weakArgs_131_, v_traceArgs_132_, v___x_133_, v_staticLib_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object* v_weakArgs_203_, lean_object* v_traceArgs_204_, lean_object* v___x_205_, lean_object* v_staticLib_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lake_buildLeanSharedLibOfStatic___lam__0(v_weakArgs_203_, v_traceArgs_204_, v___x_205_, v_staticLib_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec_ref(v_traceArgs_204_);
lean_dec_ref(v_weakArgs_203_);
return v_res_214_;
}
}
uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(lean_object* v_as_215_, size_t v_i_216_, size_t v_stop_217_, uint64_t v_b_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = lean_usize_dec_eq(v_i_216_, v_stop_217_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; uint64_t v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; size_t v___x_225_; size_t v___x_226_; 
v___x_220_ = lean_array_uget_borrowed(v_as_215_, v_i_216_);
v___x_221_ = l_Lake_Hash_nil;
v___x_222_ = lean_string_hash(v___x_220_);
v___x_223_ = lean_uint64_mix_hash(v___x_221_, v___x_222_);
v___x_224_ = lean_uint64_mix_hash(v_b_218_, v___x_223_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_add(v_i_216_, v___x_225_);
v_i_216_ = v___x_226_;
v_b_218_ = v___x_224_;
goto _start;
}
else
{
return v_b_218_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_215_ = stack[0].m_obj;
size_t v_i_216_ = stack[1].m_num;
size_t v_stop_217_ = stack[2].m_num;
uint64_t v_b_218_ = stack[3].m_num;
uint64_t v_res_228_;
v_res_228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_as_215_, v_i_216_, v_stop_217_, v_b_218_);
stack->m_num = v_res_228_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_stop_231_, lean_object* v_b_232_){
_start:
{
size_t v_i_boxed_233_; size_t v_stop_boxed_234_; uint64_t v_b_boxed_235_; uint64_t v_res_236_; lean_object* v_r_237_; 
v_i_boxed_233_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_stop_boxed_234_ = lean_unbox_usize(v_stop_231_);
lean_dec(v_stop_231_);
v_b_boxed_235_ = lean_unbox_uint64(v_b_232_);
lean_dec_ref(v_b_232_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_as_229_, v_i_boxed_233_, v_stop_boxed_234_, v_b_boxed_235_);
lean_dec_ref(v_as_229_);
v_r_237_ = lean_box_uint64(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
return v_x_239_;
}
else
{
lean_object* v_head_241_; lean_object* v_tail_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_head_241_ = lean_ctor_get(v_x_240_, 0);
v_tail_242_ = lean_ctor_get(v_x_240_, 1);
v___x_243_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0));
v___x_244_ = lean_string_append(v_x_239_, v___x_243_);
v___x_245_ = lean_string_append(v___x_244_, v_head_241_);
v_x_239_ = v___x_245_;
v_x_240_ = v_tail_242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v_x_247_, v_x_248_);
lean_dec(v_x_248_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v___x_254_; 
v___x_254_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0));
return v___x_254_;
}
else
{
lean_object* v_tail_255_; 
v_tail_255_ = lean_ctor_get(v_x_253_, 1);
if (lean_obj_tag(v_tail_255_) == 0)
{
lean_object* v_head_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_head_256_ = lean_ctor_get(v_x_253_, 0);
v___x_257_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_258_ = lean_string_append(v___x_257_, v_head_256_);
v___x_259_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2));
v___x_260_ = lean_string_append(v___x_258_, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v_head_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint32_t v___x_265_; lean_object* v___x_266_; 
v_head_261_ = lean_ctor_get(v_x_253_, 0);
v___x_262_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_263_ = lean_string_append(v___x_262_, v_head_261_);
v___x_264_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v___x_263_, v_tail_255_);
v___x_265_ = 93;
v___x_266_ = lean_string_push(v___x_264_, v___x_265_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(lean_object* v_x_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v_x_267_);
lean_dec(v_x_267_);
return v_res_268_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_nat_to_int(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4(void){
_start:
{
uint32_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = 0;
v___x_276_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3);
v___x_277_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set_uint32(v___x_277_, sizeof(void*)*1, v___x_275_);
return v___x_277_;
}
}
lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object* v_traceArgs_278_, lean_object* v_weakArgs_279_, lean_object* v_staticLib_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_log_288_; uint8_t v_action_289_; uint8_t v_wantsRebuild_290_; uint8_t v_canceled_291_; lean_object* v_trace_292_; lean_object* v_buildTime_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_346_; 
v_log_288_ = lean_ctor_get(v___y_286_, 0);
v_action_289_ = lean_ctor_get_uint8(v___y_286_, sizeof(void*)*3);
v_wantsRebuild_290_ = lean_ctor_get_uint8(v___y_286_, sizeof(void*)*3 + 1);
v_canceled_291_ = lean_ctor_get_uint8(v___y_286_, sizeof(void*)*3 + 2);
v_trace_292_ = lean_ctor_get(v___y_286_, 1);
v_buildTime_293_ = lean_ctor_get(v___y_286_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v___y_286_);
if (v_isSharedCheck_346_ == 0)
{
v___x_295_ = v___y_286_;
v_isShared_296_ = v_isSharedCheck_346_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_buildTime_293_);
lean_inc(v_trace_292_);
lean_inc(v_log_288_);
lean_dec(v___y_286_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_346_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_leanTrace_297_; lean_object* v___x_298_; uint64_t v___y_300_; uint64_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_leanTrace_297_ = lean_ctor_get(v___y_285_, 2);
lean_inc_ref(v_leanTrace_297_);
v___x_298_ = l_Lake_BuildTrace_mix(v_trace_292_, v_leanTrace_297_);
v___x_339_ = l_Lake_Hash_nil;
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_array_get_size(v_traceArgs_278_);
v___x_342_ = lean_nat_dec_lt(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
v___y_300_ = v___x_339_;
goto v___jp_299_;
}
else
{
size_t v___x_343_; size_t v___x_344_; uint64_t v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_341_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_278_, v___x_343_, v___x_344_, v___x_339_);
v___y_300_ = v___x_345_;
goto v___jp_299_;
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_301_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0));
v___x_302_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1));
lean_inc_ref(v_traceArgs_278_);
v___x_303_ = lean_array_to_list(v_traceArgs_278_);
v___x_304_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v___x_303_);
lean_dec(v___x_303_);
v___x_305_ = lean_string_append(v___x_302_, v___x_304_);
lean_dec_ref(v___x_304_);
v___x_306_ = lean_string_append(v___x_301_, v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2));
v___x_308_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4);
v___x_309_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_309_, 0, v___x_306_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_308_);
lean_ctor_set_uint64(v___x_309_, sizeof(void*)*3, v___y_300_);
v___x_310_ = l_Lake_BuildTrace_mix(v___x_298_, v___x_309_);
v___x_311_ = l_Lake_platformTrace;
v___x_312_ = l_Lake_BuildTrace_mix(v___x_310_, v___x_311_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_312_);
v___x_314_ = v___x_295_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_log_288_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_buildTime_293_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*3, v_action_289_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*3 + 1, v_wantsRebuild_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_338_, sizeof(void*)*3 + 2, v_canceled_291_);
v___x_314_ = v_reuseFailAlloc_338_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___f_317_; uint8_t v___x_318_; lean_object* v___x_319_; 
v___x_315_ = l_Lake_sharedLibExt;
lean_inc_ref(v_staticLib_280_);
v___x_316_ = l_System_FilePath_withExtension(v_staticLib_280_, v___x_315_);
lean_inc_ref_n(v___x_316_, 2);
v___f_317_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed), 11, 4);
lean_closure_set(v___f_317_, 0, v_weakArgs_279_);
lean_closure_set(v___f_317_, 1, v_traceArgs_278_);
lean_closure_set(v___f_317_, 2, v___x_316_);
lean_closure_set(v___f_317_, 3, v_staticLib_280_);
v___x_318_ = 0;
v___x_319_ = l_Lake_buildFileUnlessUpToDate_x27(v___x_316_, v___f_317_, v___x_318_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___x_314_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_319_, 0);
lean_dec(v_unused_328_);
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_316_);
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_a_329_; lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v___x_316_);
v_a_329_ = lean_ctor_get(v___x_319_, 0);
v_a_330_ = lean_ctor_get(v___x_319_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_319_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_inc(v_a_329_);
lean_dec(v___x_319_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_329_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_buildLeanSharedLibOfStatic___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_traceArgs_278_ = stack[0].m_obj;
lean_object* v_weakArgs_279_ = stack[1].m_obj;
lean_object* v_staticLib_280_ = stack[2].m_obj;
lean_object* v___y_281_ = stack[3].m_obj;
lean_object* v___y_282_ = stack[4].m_obj;
lean_object* v___y_283_ = stack[5].m_obj;
lean_object* v___y_284_ = stack[6].m_obj;
lean_object* v___y_285_ = stack[7].m_obj;
lean_object* v___y_286_ = stack[8].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lake_buildLeanSharedLibOfStatic___lam__1(v_traceArgs_278_, v_weakArgs_279_, v_staticLib_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object* v_traceArgs_348_, lean_object* v_weakArgs_349_, lean_object* v_staticLib_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lake_buildLeanSharedLibOfStatic___lam__1(v_traceArgs_348_, v_weakArgs_349_, v_staticLib_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec(v___y_353_);
lean_dec(v___y_352_);
return v_res_358_;
}
}
lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* v_staticLibJob_359_, lean_object* v_weakArgs_360_, lean_object* v_traceArgs_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; 
v___f_369_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed), 10, 2);
lean_closure_set(v___f_369_, 0, v_traceArgs_361_);
lean_closure_set(v___f_369_, 1, v_weakArgs_360_);
v___x_370_ = l_Lake_instDataKindFilePath;
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = 0;
v___x_373_ = l_Lake_Job_mapM___redArg(v___x_370_, v_staticLibJob_359_, v___f_369_, v___x_371_, v___x_372_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_373_;
}
}
LEAN_EXPORT void l_Lake_buildLeanSharedLibOfStatic_0interp(lean_interpreter_value* stack)
{
lean_object* v_staticLibJob_359_ = stack[0].m_obj;
lean_object* v_weakArgs_360_ = stack[1].m_obj;
lean_object* v_traceArgs_361_ = stack[2].m_obj;
lean_object* v_a_362_ = stack[3].m_obj;
lean_object* v_a_363_ = stack[4].m_obj;
lean_object* v_a_364_ = stack[5].m_obj;
lean_object* v_a_365_ = stack[6].m_obj;
lean_object* v_a_366_ = stack[7].m_obj;
lean_object* v_a_367_ = stack[8].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lake_buildLeanSharedLibOfStatic(v_staticLibJob_359_, v_weakArgs_360_, v_traceArgs_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object* v_staticLibJob_375_, lean_object* v_weakArgs_376_, lean_object* v_traceArgs_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lake_buildLeanSharedLibOfStatic(v_staticLibJob_375_, v_weakArgs_376_, v_traceArgs_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec_ref(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec(v_a_380_);
lean_dec(v_a_379_);
return v_res_385_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1));
v___x_390_ = l_Lake_BuildTrace_nil(v___x_389_);
return v___x_390_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object* v___x_391_, lean_object* v_config_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
lean_inc_ref(v___y_393_);
lean_inc_ref(v___y_397_);
lean_inc(v___y_396_);
lean_inc(v___y_395_);
lean_inc(v___y_394_);
v___x_400_ = lean_apply_7(v___y_393_, v___x_391_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, lean_box(0));
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_toLeanConfig_401_; lean_object* v_a_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_414_; 
v_toLeanConfig_401_ = lean_ctor_get(v_config_392_, 1);
lean_inc_ref(v_toLeanConfig_401_);
lean_dec_ref(v_config_392_);
v_a_402_ = lean_ctor_get(v___x_400_, 0);
v_a_403_ = lean_ctor_get(v___x_400_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_414_ == 0)
{
v___x_405_ = v___x_400_;
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_inc(v_a_402_);
lean_dec(v___x_400_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v_moreLinkArgs_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v_moreLinkArgs_407_ = lean_ctor_get(v_toLeanConfig_401_, 8);
lean_inc_ref(v_moreLinkArgs_407_);
lean_dec_ref(v_toLeanConfig_401_);
v___x_408_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0));
v___x_409_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_410_ = l_Lake_buildLeanSharedLibOfStatic(v_a_402_, v_moreLinkArgs_407_, v___x_408_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___x_409_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_410_);
v___x_412_ = v___x_405_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_a_403_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_dec_ref(v___y_393_);
lean_dec_ref(v_config_392_);
return v___x_400_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_391_ = stack[0].m_obj;
lean_object* v_config_392_ = stack[1].m_obj;
lean_object* v___y_393_ = stack[2].m_obj;
lean_object* v___y_394_ = stack[3].m_obj;
lean_object* v___y_395_ = stack[4].m_obj;
lean_object* v___y_396_ = stack[5].m_obj;
lean_object* v___y_397_ = stack[6].m_obj;
lean_object* v___y_398_ = stack[7].m_obj;
lean_object* v_res_415_;
v_res_415_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(v___x_391_, v_config_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object* v___x_416_, lean_object* v_config_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(v___x_416_, v_config_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec(v___y_420_);
lean_dec(v___y_419_);
return v_res_425_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object* v_lib_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_pkg_435_; lean_object* v_name_436_; lean_object* v_keyName_437_; lean_object* v_config_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___f_450_; uint8_t v___x_451_; lean_object* v___x_452_; 
v_pkg_435_ = lean_ctor_get(v_lib_427_, 0);
v_name_436_ = lean_ctor_get(v_lib_427_, 1);
v_keyName_437_ = lean_ctor_get(v_pkg_435_, 2);
v_config_438_ = lean_ctor_get(v_pkg_435_, 6);
lean_inc_ref(v_config_438_);
v___x_439_ = l_Lake_instDataKindFilePath;
v___x_440_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
lean_inc_n(v_name_436_, 2);
v___x_441_ = l_Lean_Name_str___override(v_name_436_, v___x_440_);
v___x_442_ = 1;
v___x_443_ = l_Lean_Name_toString(v___x_441_, v___x_442_);
v___x_444_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0));
v___x_445_ = lean_string_append(v___x_443_, v___x_444_);
v___x_446_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_keyName_437_);
v___x_447_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_447_, 0, v_keyName_437_);
lean_ctor_set(v___x_447_, 1, v_name_436_);
v___x_448_ = l_Lake_ExternLib_keyword;
v___x_449_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
lean_ctor_set(v___x_449_, 2, v_lib_427_);
lean_ctor_set(v___x_449_, 3, v___x_446_);
v___f_450_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed), 9, 2);
lean_closure_set(v___f_450_, 0, v___x_449_);
lean_closure_set(v___f_450_, 1, v_config_438_);
v___x_451_ = 0;
v___x_452_ = l_Lake_ensureJob___redArg(v___x_439_, v___f_450_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_477_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
v_a_454_ = lean_ctor_get(v___x_452_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_477_ == 0)
{
v___x_456_ = v___x_452_;
v_isShared_457_ = v_isSharedCheck_477_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_inc(v_a_453_);
lean_dec(v___x_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_477_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_task_458_; lean_object* v_kind_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_475_; 
v_task_458_ = lean_ctor_get(v_a_453_, 0);
v_kind_459_ = lean_ctor_get(v_a_453_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v_a_453_, 2);
lean_dec(v_unused_476_);
v___x_461_ = v_a_453_;
v_isShared_462_ = v_isSharedCheck_475_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_kind_459_);
lean_inc(v_task_458_);
lean_dec(v_a_453_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_475_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v_registeredJobs_463_; lean_object* v_job_465_; 
v_registeredJobs_463_ = lean_ctor_get(v_a_432_, 4);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 2, v___x_445_);
v_job_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_task_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_kind_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v___x_445_);
v_job_465_ = v_reuseFailAlloc_474_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
lean_ctor_set_uint8(v_job_465_, sizeof(void*)*3, v___x_451_);
v___x_466_ = lean_st_ref_take(v_registeredJobs_463_);
lean_inc_ref(v_job_465_);
v___x_467_ = l_Lake_Job_toOpaque___redArg(v_job_465_);
v___x_468_ = lean_array_push(v___x_466_, v___x_467_);
v___x_469_ = lean_st_ref_put(v_registeredJobs_463_, v___x_468_);
v___x_470_ = l_Lake_Job_renew___redArg(v_job_465_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_470_);
v___x_472_ = v___x_456_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_a_454_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_445_);
return v___x_452_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_lib_427_ = stack[0].m_obj;
lean_object* v_a_428_ = stack[1].m_obj;
lean_object* v_a_429_ = stack[2].m_obj;
lean_object* v_a_430_ = stack[3].m_obj;
lean_object* v_a_431_ = stack[4].m_obj;
lean_object* v_a_432_ = stack[5].m_obj;
lean_object* v_a_433_ = stack[6].m_obj;
lean_object* v_res_478_;
v_res_478_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(v_lib_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object* v_lib_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(v_lib_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec(v_a_482_);
lean_dec(v_a_481_);
return v_res_487_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___f_489_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_490_ = 1;
v___x_491_ = l_Lake_instDataKindFilePath;
v___x_492_ = ((lean_object*)(l_Lake_ExternLib_sharedFacetConfig___closed__0));
v___x_493_ = l_Lake_ExternLib_keyword;
v___x_494_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_491_);
lean_ctor_set(v___x_494_, 3, v___f_489_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*4, v___x_490_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*4 + 1, v___x_490_);
return v___x_494_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lake_ExternLib_sharedFacetConfig___closed__1, &l_Lake_ExternLib_sharedFacetConfig___closed__1_once, _init_l_Lake_ExternLib_sharedFacetConfig___closed__1);
return v___x_495_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object* v_sharedLib_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_533_; 
lean_inc_ref(v_sharedLib_502_);
v___x_533_ = l_System_FilePath_fileStem(v_sharedLib_502_);
if (lean_obj_tag(v___x_533_) == 1)
{
lean_object* v_val_534_; uint8_t v___x_535_; 
v_val_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v___x_533_, 1);
v___x_535_ = l_System_Platform_isWindows;
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_string_utf8_byte_size(v_val_534_);
v___x_537_ = lean_unsigned_to_nat(3u);
v___x_538_ = lean_nat_dec_le(v___x_537_, v___x_536_);
if (v___x_538_ == 0)
{
lean_dec(v_val_534_);
goto v___jp_510_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_539_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_string_memcmp(v_val_534_, v___x_539_, v___x_540_, v___x_540_, v___x_537_);
if (v___x_541_ == 0)
{
lean_dec(v_val_534_);
goto v___jp_510_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_inc(v_val_534_);
v___x_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_542_, 0, v_val_534_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_ctor_set(v___x_542_, 2, v___x_536_);
v___x_543_ = l_String_Slice_Pos_nextn(v___x_542_, v___x_540_, v___x_537_);
lean_dec_ref_known(v___x_542_, 3);
v___x_544_ = lean_string_utf8_extract_fast(v_val_534_, v___x_543_, v___x_536_);
lean_dec(v___x_543_);
lean_dec(v_val_534_);
v___x_545_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3));
v___x_546_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_546_, 0, v_sharedLib_502_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
lean_ctor_set(v___x_546_, 3, v___x_545_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*4, v___x_535_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___y_508_);
return v___x_547_;
}
}
}
else
{
uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = 0;
v___x_549_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3));
v___x_550_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_550_, 0, v_sharedLib_502_);
lean_ctor_set(v___x_550_, 1, v_val_534_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_ctor_set(v___x_550_, 3, v___x_549_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*4, v___x_548_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___y_508_);
return v___x_551_;
}
}
else
{
lean_object* v_log_552_; uint8_t v_action_553_; uint8_t v_wantsRebuild_554_; uint8_t v_canceled_555_; lean_object* v_trace_556_; lean_object* v_buildTime_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_573_; 
lean_dec(v___x_533_);
v_log_552_ = lean_ctor_get(v___y_508_, 0);
v_action_553_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*3);
v_wantsRebuild_554_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*3 + 1);
v_canceled_555_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*3 + 2);
v_trace_556_ = lean_ctor_get(v___y_508_, 1);
v_buildTime_557_ = lean_ctor_get(v___y_508_, 2);
v_isSharedCheck_573_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_573_ == 0)
{
v___x_559_ = v___y_508_;
v_isShared_560_ = v_isSharedCheck_573_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_buildTime_557_);
lean_inc(v_trace_556_);
lean_inc(v_log_552_);
lean_dec(v___y_508_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_573_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_561_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_562_ = lean_string_append(v___x_561_, v_sharedLib_502_);
lean_dec_ref(v_sharedLib_502_);
v___x_563_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4));
v___x_564_ = lean_string_append(v___x_562_, v___x_563_);
v___x_565_ = 3;
v___x_566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_565_);
v___x_567_ = lean_array_get_size(v_log_552_);
v___x_568_ = lean_array_push(v_log_552_, v___x_566_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_568_);
v___x_570_ = v___x_559_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_trace_556_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_buildTime_557_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*3, v_action_553_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*3 + 1, v_wantsRebuild_554_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*3 + 2, v_canceled_555_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_567_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
}
}
v___jp_510_:
{
lean_object* v_log_511_; uint8_t v_action_512_; uint8_t v_wantsRebuild_513_; uint8_t v_canceled_514_; lean_object* v_trace_515_; lean_object* v_buildTime_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_532_; 
v_log_511_ = lean_ctor_get(v___y_508_, 0);
v_action_512_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*3);
v_wantsRebuild_513_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*3 + 1);
v_canceled_514_ = lean_ctor_get_uint8(v___y_508_, sizeof(void*)*3 + 2);
v_trace_515_ = lean_ctor_get(v___y_508_, 1);
v_buildTime_516_ = lean_ctor_get(v___y_508_, 2);
v_isSharedCheck_532_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_532_ == 0)
{
v___x_518_ = v___y_508_;
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_buildTime_516_);
lean_inc(v_trace_515_);
lean_inc(v_log_511_);
lean_dec(v___y_508_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_532_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_520_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_521_ = lean_string_append(v___x_520_, v_sharedLib_502_);
lean_dec_ref(v_sharedLib_502_);
v___x_522_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1));
v___x_523_ = lean_string_append(v___x_521_, v___x_522_);
v___x_524_ = 3;
v___x_525_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1, v___x_524_);
v___x_526_ = lean_array_get_size(v_log_511_);
v___x_527_ = lean_array_push(v_log_511_, v___x_525_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_527_);
v___x_529_ = v___x_518_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_trace_515_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_buildTime_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*3, v_action_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*3 + 1, v_wantsRebuild_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*3 + 2, v_canceled_514_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_526_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_sharedLib_502_ = stack[0].m_obj;
lean_object* v___y_503_ = stack[1].m_obj;
lean_object* v___y_504_ = stack[2].m_obj;
lean_object* v___y_505_ = stack[3].m_obj;
lean_object* v___y_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v_res_574_;
v_res_574_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(v_sharedLib_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object* v_sharedLib_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(v_sharedLib_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_583_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object* v_sharedLibTarget_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; 
v___f_593_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0));
v___x_594_ = l_Lake_instDataKindDynlib;
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = 0;
v___x_597_ = l_Lake_Job_mapM___redArg(v___x_594_, v_sharedLibTarget_585_, v___f_593_, v___x_595_, v___x_596_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
return v___x_597_;
}
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_sharedLibTarget_585_ = stack[0].m_obj;
lean_object* v_a_586_ = stack[1].m_obj;
lean_object* v_a_587_ = stack[2].m_obj;
lean_object* v_a_588_ = stack[3].m_obj;
lean_object* v_a_589_ = stack[4].m_obj;
lean_object* v_a_590_ = stack[5].m_obj;
lean_object* v_a_591_ = stack[6].m_obj;
lean_object* v_res_598_;
v_res_598_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_sharedLibTarget_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object* v_sharedLibTarget_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_sharedLibTarget_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec_ref(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec(v_a_602_);
lean_dec(v_a_601_);
return v_res_607_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object* v___x_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; 
lean_inc_ref(v___y_609_);
lean_inc_ref(v___y_613_);
lean_inc(v___y_612_);
lean_inc(v___y_611_);
lean_inc(v___y_610_);
v___x_616_ = lean_apply_7(v___y_609_, v___x_608_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, lean_box(0));
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_627_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_a_618_ = lean_ctor_get(v___x_616_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_627_ == 0)
{
v___x_620_ = v___x_616_;
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_627_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_622_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_623_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_a_617_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___x_622_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_623_);
v___x_625_ = v___x_620_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_a_618_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v___y_609_);
v_a_628_ = lean_ctor_get(v___x_616_, 0);
v_a_629_ = lean_ctor_get(v___x_616_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_616_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_inc(v_a_628_);
lean_dec(v___x_616_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_628_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_a_629_);
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
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_608_ = stack[0].m_obj;
lean_object* v___y_609_ = stack[1].m_obj;
lean_object* v___y_610_ = stack[2].m_obj;
lean_object* v___y_611_ = stack[3].m_obj;
lean_object* v___y_612_ = stack[4].m_obj;
lean_object* v___y_613_ = stack[5].m_obj;
lean_object* v___y_614_ = stack[6].m_obj;
lean_object* v_res_637_;
v_res_637_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(v___x_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object* v___x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(v___x_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec(v___y_641_);
lean_dec(v___y_640_);
return v_res_646_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object* v_lib_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_pkg_656_; lean_object* v_name_657_; lean_object* v_keyName_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___f_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v_pkg_656_ = lean_ctor_get(v_lib_648_, 0);
v_name_657_ = lean_ctor_get(v_lib_648_, 1);
v_keyName_658_ = lean_ctor_get(v_pkg_656_, 2);
v___x_659_ = l_Lake_instDataKindDynlib;
v___x_660_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
lean_inc_n(v_name_657_, 2);
v___x_661_ = l_Lean_Name_str___override(v_name_657_, v___x_660_);
v___x_662_ = 1;
v___x_663_ = l_Lean_Name_toString(v___x_661_, v___x_662_);
v___x_664_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0));
v___x_665_ = lean_string_append(v___x_663_, v___x_664_);
v___x_666_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_keyName_658_);
v___x_667_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_667_, 0, v_keyName_658_);
lean_ctor_set(v___x_667_, 1, v_name_657_);
v___x_668_ = l_Lake_ExternLib_keyword;
v___x_669_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_ctor_set(v___x_669_, 2, v_lib_648_);
lean_ctor_set(v___x_669_, 3, v___x_666_);
v___f_670_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed), 8, 1);
lean_closure_set(v___f_670_, 0, v___x_669_);
v___x_671_ = 0;
v___x_672_ = l_Lake_ensureJob___redArg(v___x_659_, v___f_670_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_697_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_a_674_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_697_ == 0)
{
v___x_676_ = v___x_672_;
v_isShared_677_ = v_isSharedCheck_697_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_697_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_task_678_; lean_object* v_kind_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_695_; 
v_task_678_ = lean_ctor_get(v_a_673_, 0);
v_kind_679_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_a_673_, 2);
lean_dec(v_unused_696_);
v___x_681_ = v_a_673_;
v_isShared_682_ = v_isSharedCheck_695_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_kind_679_);
lean_inc(v_task_678_);
lean_dec(v_a_673_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_695_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_registeredJobs_683_; lean_object* v_job_685_; 
v_registeredJobs_683_ = lean_ctor_get(v_a_653_, 4);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v___x_665_);
v_job_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_task_678_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_kind_679_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v___x_665_);
v_job_685_ = v_reuseFailAlloc_694_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
lean_ctor_set_uint8(v_job_685_, sizeof(void*)*3, v___x_671_);
v___x_686_ = lean_st_ref_take(v_registeredJobs_683_);
lean_inc_ref(v_job_685_);
v___x_687_ = l_Lake_Job_toOpaque___redArg(v_job_685_);
v___x_688_ = lean_array_push(v___x_686_, v___x_687_);
v___x_689_ = lean_st_ref_put(v_registeredJobs_683_, v___x_688_);
v___x_690_ = l_Lake_Job_renew___redArg(v_job_685_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_690_);
v___x_692_ = v___x_676_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_a_674_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_665_);
return v___x_672_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib_0interp(lean_interpreter_value* stack)
{
lean_object* v_lib_648_ = stack[0].m_obj;
lean_object* v_a_649_ = stack[1].m_obj;
lean_object* v_a_650_ = stack[2].m_obj;
lean_object* v_a_651_ = stack[3].m_obj;
lean_object* v_a_652_ = stack[4].m_obj;
lean_object* v_a_653_ = stack[5].m_obj;
lean_object* v_a_654_ = stack[6].m_obj;
lean_object* v_res_698_;
v_res_698_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(v_lib_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object* v_lib_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(v_lib_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec(v_a_702_);
lean_dec(v_a_701_);
return v_res_707_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t v_fmt_708_, lean_object* v_a_709_){
_start:
{
if (v_fmt_708_ == 0)
{
lean_object* v_path_710_; 
v_path_710_ = lean_ctor_get(v_a_709_, 0);
lean_inc_ref(v_path_710_);
return v_path_710_;
}
else
{
lean_object* v_path_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_path_711_ = lean_ctor_get(v_a_709_, 0);
lean_inc_ref(v_path_711_);
v___x_712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_712_, 0, v_path_711_);
v___x_713_ = l_Lean_Json_compress(v___x_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_708_ = stack[0].m_num;
lean_object* v_a_709_ = stack[1].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(v_fmt_708_, v_a_709_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object* v_fmt_715_, lean_object* v_a_716_){
_start:
{
uint8_t v_fmt_boxed_717_; lean_object* v_res_718_; 
v_fmt_boxed_717_ = lean_unbox(v_fmt_715_);
v_res_718_ = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(v_fmt_boxed_717_, v_a_716_);
lean_dec_ref(v_a_716_);
return v_res_718_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___f_721_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__0));
v___x_722_ = 1;
v___x_723_ = l_Lake_instDataKindDynlib;
v___x_724_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__1));
v___x_725_ = l_Lake_ExternLib_keyword;
v___x_726_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_723_);
lean_ctor_set(v___x_726_, 3, v___f_721_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*4, v___x_722_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*4 + 1, v___x_722_);
return v___x_726_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig(void){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_obj_once(&l_Lake_ExternLib_dynlibFacetConfig___closed__2, &l_Lake_ExternLib_dynlibFacetConfig___closed__2_once, _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2);
return v___x_727_;
}
}
lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object* v_lib_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_pkg_736_; lean_object* v_name_737_; lean_object* v_keyName_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_pkg_736_ = lean_ctor_get(v_lib_728_, 0);
v_name_737_ = lean_ctor_get(v_lib_728_, 1);
v_keyName_738_ = lean_ctor_get(v_pkg_736_, 2);
v___x_739_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_737_);
lean_inc(v_keyName_738_);
v___x_740_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_740_, 0, v_keyName_738_);
lean_ctor_set(v___x_740_, 1, v_name_737_);
v___x_741_ = l_Lake_ExternLib_keyword;
v___x_742_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
lean_ctor_set(v___x_742_, 2, v_lib_728_);
lean_ctor_set(v___x_742_, 3, v___x_739_);
lean_inc_ref(v_a_733_);
lean_inc(v_a_732_);
lean_inc(v_a_731_);
lean_inc(v_a_730_);
v___x_743_ = lean_apply_7(v_a_729_, v___x_742_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, lean_box(0));
return v___x_743_;
}
}
LEAN_EXPORT void l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_lib_728_ = stack[0].m_obj;
lean_object* v_a_729_ = stack[1].m_obj;
lean_object* v_a_730_ = stack[2].m_obj;
lean_object* v_a_731_ = stack[3].m_obj;
lean_object* v_a_732_ = stack[4].m_obj;
lean_object* v_a_733_ = stack[5].m_obj;
lean_object* v_a_734_ = stack[6].m_obj;
lean_object* v_res_744_;
v_res_744_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(v_lib_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object* v_lib_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(v_lib_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec(v_a_748_);
lean_dec(v_a_747_);
return v_res_753_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_755_; lean_object* v___f_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_755_ = 0;
v___f_756_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_757_ = 1;
v___x_758_ = l_Lake_instDataKindFilePath;
v___x_759_ = ((lean_object*)(l_Lake_ExternLib_defaultFacetConfig___closed__0));
v___x_760_ = l_Lake_ExternLib_keyword;
v___x_761_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_759_);
lean_ctor_set(v___x_761_, 2, v___x_758_);
lean_ctor_set(v___x_761_, 3, v___f_756_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*4, v___x_757_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*4 + 1, v___x_755_);
return v___x_761_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_obj_once(&l_Lake_ExternLib_defaultFacetConfig___closed__1, &l_Lake_ExternLib_defaultFacetConfig___closed__1_once, _init_l_Lake_ExternLib_defaultFacetConfig___closed__1);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_763_, lean_object* v_v_764_, lean_object* v_t_765_){
_start:
{
if (lean_obj_tag(v_t_765_) == 0)
{
lean_object* v_size_766_; lean_object* v_k_767_; lean_object* v_v_768_; lean_object* v_l_769_; lean_object* v_r_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_1050_; 
v_size_766_ = lean_ctor_get(v_t_765_, 0);
v_k_767_ = lean_ctor_get(v_t_765_, 1);
v_v_768_ = lean_ctor_get(v_t_765_, 2);
v_l_769_ = lean_ctor_get(v_t_765_, 3);
v_r_770_ = lean_ctor_get(v_t_765_, 4);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_t_765_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_772_ = v_t_765_;
v_isShared_773_ = v_isSharedCheck_1050_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_r_770_);
lean_inc(v_l_769_);
lean_inc(v_v_768_);
lean_inc(v_k_767_);
lean_inc(v_size_766_);
lean_dec(v_t_765_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_1050_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
uint8_t v___x_774_; 
v___x_774_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_763_, v_k_767_);
switch(v___x_774_)
{
case 0:
{
lean_object* v_impl_775_; lean_object* v___x_776_; 
lean_dec(v_size_766_);
v_impl_775_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_763_, v_v_764_, v_l_769_);
v___x_776_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_770_) == 0)
{
lean_object* v_size_777_; lean_object* v_size_778_; lean_object* v_k_779_; lean_object* v_v_780_; lean_object* v_l_781_; lean_object* v_r_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_size_777_ = lean_ctor_get(v_r_770_, 0);
v_size_778_ = lean_ctor_get(v_impl_775_, 0);
v_k_779_ = lean_ctor_get(v_impl_775_, 1);
v_v_780_ = lean_ctor_get(v_impl_775_, 2);
v_l_781_ = lean_ctor_get(v_impl_775_, 3);
v_r_782_ = lean_ctor_get(v_impl_775_, 4);
lean_inc(v_r_782_);
v___x_783_ = lean_unsigned_to_nat(3u);
v___x_784_ = lean_nat_mul(v___x_783_, v_size_777_);
v___x_785_ = lean_nat_dec_lt(v___x_784_, v_size_778_);
lean_dec(v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_r_782_);
v___x_786_ = lean_nat_add(v___x_776_, v_size_778_);
v___x_787_ = lean_nat_add(v___x_786_, v_size_777_);
lean_dec(v___x_786_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 3, v_impl_775_);
lean_ctor_set(v___x_772_, 0, v___x_787_);
v___x_789_ = v___x_772_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v_impl_775_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_r_770_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_856_; 
lean_inc(v_l_781_);
lean_inc(v_v_780_);
lean_inc(v_k_779_);
lean_inc(v_size_778_);
v_isSharedCheck_856_ = !lean_is_exclusive(v_impl_775_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; lean_object* v_unused_861_; 
v_unused_857_ = lean_ctor_get(v_impl_775_, 4);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_impl_775_, 3);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_impl_775_, 2);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_impl_775_, 1);
lean_dec(v_unused_860_);
v_unused_861_ = lean_ctor_get(v_impl_775_, 0);
lean_dec(v_unused_861_);
v___x_792_ = v_impl_775_;
v_isShared_793_ = v_isSharedCheck_856_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_impl_775_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_856_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_size_794_; lean_object* v_size_795_; lean_object* v_k_796_; lean_object* v_v_797_; lean_object* v_l_798_; lean_object* v_r_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_size_794_ = lean_ctor_get(v_l_781_, 0);
v_size_795_ = lean_ctor_get(v_r_782_, 0);
v_k_796_ = lean_ctor_get(v_r_782_, 1);
v_v_797_ = lean_ctor_get(v_r_782_, 2);
v_l_798_ = lean_ctor_get(v_r_782_, 3);
v_r_799_ = lean_ctor_get(v_r_782_, 4);
v___x_800_ = lean_unsigned_to_nat(2u);
v___x_801_ = lean_nat_mul(v___x_800_, v_size_794_);
v___x_802_ = lean_nat_dec_lt(v_size_795_, v___x_801_);
lean_dec(v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_831_; 
lean_inc(v_r_799_);
lean_inc(v_l_798_);
lean_inc(v_v_797_);
lean_inc(v_k_796_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_r_782_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_832_ = lean_ctor_get(v_r_782_, 4);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_782_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_782_, 2);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_782_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_r_782_, 0);
lean_dec(v_unused_836_);
v___x_804_ = v_r_782_;
v_isShared_805_ = v_isSharedCheck_831_;
goto v_resetjp_803_;
}
else
{
lean_dec(v_r_782_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_831_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___x_819_; lean_object* v___y_821_; 
v___x_806_ = lean_nat_add(v___x_776_, v_size_778_);
lean_dec(v_size_778_);
v___x_807_ = lean_nat_add(v___x_806_, v_size_777_);
lean_dec(v___x_806_);
v___x_819_ = lean_nat_add(v___x_776_, v_size_794_);
if (lean_obj_tag(v_l_798_) == 0)
{
lean_object* v_size_829_; 
v_size_829_ = lean_ctor_get(v_l_798_, 0);
lean_inc(v_size_829_);
v___y_821_ = v_size_829_;
goto v___jp_820_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___y_821_ = v___x_830_;
goto v___jp_820_;
}
v___jp_808_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_nat_add(v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec(v___y_810_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v_r_770_);
lean_ctor_set(v___x_804_, 3, v_r_799_);
lean_ctor_set(v___x_804_, 2, v_v_768_);
lean_ctor_set(v___x_804_, 1, v_k_767_);
lean_ctor_set(v___x_804_, 0, v___x_812_);
v___x_814_ = v___x_804_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_r_799_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_r_770_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v___x_814_);
lean_ctor_set(v___x_792_, 3, v___y_809_);
lean_ctor_set(v___x_792_, 2, v_v_797_);
lean_ctor_set(v___x_792_, 1, v_k_796_);
lean_ctor_set(v___x_792_, 0, v___x_807_);
v___x_816_ = v___x_792_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_k_796_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_v_797_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v___y_809_);
lean_ctor_set(v_reuseFailAlloc_817_, 4, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_nat_add(v___x_819_, v___y_821_);
lean_dec(v___y_821_);
lean_dec(v___x_819_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_l_798_);
lean_ctor_set(v___x_772_, 3, v_l_781_);
lean_ctor_set(v___x_772_, 2, v_v_780_);
lean_ctor_set(v___x_772_, 1, v_k_779_);
lean_ctor_set(v___x_772_, 0, v___x_822_);
v___x_824_ = v___x_772_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_l_781_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_l_798_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; 
v___x_825_ = lean_nat_add(v___x_776_, v_size_777_);
if (lean_obj_tag(v_r_799_) == 0)
{
lean_object* v_size_826_; 
v_size_826_ = lean_ctor_get(v_r_799_, 0);
lean_inc(v_size_826_);
v___y_809_ = v___x_824_;
v___y_810_ = v___x_825_;
v___y_811_ = v_size_826_;
goto v___jp_808_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___y_809_ = v___x_824_;
v___y_810_ = v___x_825_;
v___y_811_ = v___x_827_;
goto v___jp_808_;
}
}
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
lean_del_object(v___x_772_);
v___x_837_ = lean_nat_add(v___x_776_, v_size_778_);
lean_dec(v_size_778_);
v___x_838_ = lean_nat_add(v___x_837_, v_size_777_);
lean_dec(v___x_837_);
v___x_839_ = lean_nat_add(v___x_776_, v_size_777_);
v___x_840_ = lean_nat_add(v___x_839_, v_size_795_);
lean_dec(v___x_839_);
lean_inc_ref(v_r_770_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v_r_770_);
lean_ctor_set(v___x_792_, 3, v_r_782_);
lean_ctor_set(v___x_792_, 2, v_v_768_);
lean_ctor_set(v___x_792_, 1, v_k_767_);
lean_ctor_set(v___x_792_, 0, v___x_840_);
v___x_842_ = v___x_792_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_r_782_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_r_770_);
v___x_842_ = v_reuseFailAlloc_855_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v_r_770_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; lean_object* v_unused_851_; lean_object* v_unused_852_; lean_object* v_unused_853_; lean_object* v_unused_854_; 
v_unused_850_ = lean_ctor_get(v_r_770_, 4);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_r_770_, 3);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_r_770_, 2);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_r_770_, 1);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_r_770_, 0);
lean_dec(v_unused_854_);
v___x_844_ = v_r_770_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_r_770_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v___x_842_);
lean_ctor_set(v___x_844_, 3, v_l_781_);
lean_ctor_set(v___x_844_, 2, v_v_780_);
lean_ctor_set(v___x_844_, 1, v_k_779_);
lean_ctor_set(v___x_844_, 0, v___x_838_);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v_l_781_);
lean_ctor_set(v_reuseFailAlloc_848_, 4, v___x_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_862_; 
v_l_862_ = lean_ctor_get(v_impl_775_, 3);
if (lean_obj_tag(v_l_862_) == 0)
{
lean_object* v_r_863_; lean_object* v_k_864_; lean_object* v_v_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_876_; 
lean_inc_ref(v_l_862_);
v_r_863_ = lean_ctor_get(v_impl_775_, 4);
v_k_864_ = lean_ctor_get(v_impl_775_, 1);
v_v_865_ = lean_ctor_get(v_impl_775_, 2);
v_isSharedCheck_876_ = !lean_is_exclusive(v_impl_775_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; lean_object* v_unused_878_; 
v_unused_877_ = lean_ctor_get(v_impl_775_, 3);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_impl_775_, 0);
lean_dec(v_unused_878_);
v___x_867_ = v_impl_775_;
v_isShared_868_ = v_isSharedCheck_876_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_r_863_);
lean_inc(v_v_865_);
lean_inc(v_k_864_);
lean_dec(v_impl_775_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_876_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_863_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 3, v_r_863_);
lean_ctor_set(v___x_867_, 2, v_v_768_);
lean_ctor_set(v___x_867_, 1, v_k_767_);
lean_ctor_set(v___x_867_, 0, v___x_776_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_r_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v_r_863_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v___x_871_);
lean_ctor_set(v___x_772_, 3, v_l_862_);
lean_ctor_set(v___x_772_, 2, v_v_865_);
lean_ctor_set(v___x_772_, 1, v_k_864_);
lean_ctor_set(v___x_772_, 0, v___x_869_);
v___x_873_ = v___x_772_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_k_864_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_v_865_);
lean_ctor_set(v_reuseFailAlloc_874_, 3, v_l_862_);
lean_ctor_set(v_reuseFailAlloc_874_, 4, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_r_879_; 
v_r_879_ = lean_ctor_get(v_impl_775_, 4);
lean_inc(v_r_879_);
if (lean_obj_tag(v_r_879_) == 0)
{
lean_object* v_k_880_; lean_object* v_v_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_904_; 
lean_inc(v_l_862_);
v_k_880_ = lean_ctor_get(v_impl_775_, 1);
v_v_881_ = lean_ctor_get(v_impl_775_, 2);
v_isSharedCheck_904_ = !lean_is_exclusive(v_impl_775_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; lean_object* v_unused_906_; lean_object* v_unused_907_; 
v_unused_905_ = lean_ctor_get(v_impl_775_, 4);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_impl_775_, 3);
lean_dec(v_unused_906_);
v_unused_907_ = lean_ctor_get(v_impl_775_, 0);
lean_dec(v_unused_907_);
v___x_883_ = v_impl_775_;
v_isShared_884_ = v_isSharedCheck_904_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_v_881_);
lean_inc(v_k_880_);
lean_dec(v_impl_775_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_904_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_k_885_; lean_object* v_v_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_900_; 
v_k_885_ = lean_ctor_get(v_r_879_, 1);
v_v_886_ = lean_ctor_get(v_r_879_, 2);
v_isSharedCheck_900_ = !lean_is_exclusive(v_r_879_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; lean_object* v_unused_902_; lean_object* v_unused_903_; 
v_unused_901_ = lean_ctor_get(v_r_879_, 4);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_r_879_, 3);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_r_879_, 0);
lean_dec(v_unused_903_);
v___x_888_ = v_r_879_;
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_v_886_);
lean_inc(v_k_885_);
lean_dec(v_r_879_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_900_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_unsigned_to_nat(3u);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 4, v_l_862_);
lean_ctor_set(v___x_888_, 3, v_l_862_);
lean_ctor_set(v___x_888_, 2, v_v_881_);
lean_ctor_set(v___x_888_, 1, v_k_880_);
lean_ctor_set(v___x_888_, 0, v___x_776_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_k_880_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_v_881_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_l_862_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_l_862_);
v___x_892_ = v_reuseFailAlloc_899_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 4, v_l_862_);
lean_ctor_set(v___x_883_, 2, v_v_768_);
lean_ctor_set(v___x_883_, 1, v_k_767_);
lean_ctor_set(v___x_883_, 0, v___x_776_);
v___x_894_ = v___x_883_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_l_862_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_l_862_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v___x_894_);
lean_ctor_set(v___x_772_, 3, v___x_892_);
lean_ctor_set(v___x_772_, 2, v_v_886_);
lean_ctor_set(v___x_772_, 1, v_k_885_);
lean_ctor_set(v___x_772_, 0, v___x_890_);
v___x_896_ = v___x_772_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_k_885_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_v_886_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(2u);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_r_879_);
lean_ctor_set(v___x_772_, 3, v_impl_775_);
lean_ctor_set(v___x_772_, 0, v___x_908_);
v___x_910_ = v___x_772_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_impl_775_);
lean_ctor_set(v_reuseFailAlloc_911_, 4, v_r_879_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
case 1:
{
lean_object* v___x_913_; 
lean_dec(v_v_768_);
lean_dec(v_k_767_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 2, v_v_764_);
lean_ctor_set(v___x_772_, 1, v_k_763_);
v___x_913_ = v___x_772_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_size_766_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_k_763_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_v_764_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_l_769_);
lean_ctor_set(v_reuseFailAlloc_914_, 4, v_r_770_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
default: 
{
lean_object* v_impl_915_; lean_object* v___x_916_; 
lean_dec(v_size_766_);
v_impl_915_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_763_, v_v_764_, v_r_770_);
v___x_916_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_769_) == 0)
{
lean_object* v_size_917_; lean_object* v_size_918_; lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v_l_921_; lean_object* v_r_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_size_917_ = lean_ctor_get(v_l_769_, 0);
v_size_918_ = lean_ctor_get(v_impl_915_, 0);
v_k_919_ = lean_ctor_get(v_impl_915_, 1);
v_v_920_ = lean_ctor_get(v_impl_915_, 2);
v_l_921_ = lean_ctor_get(v_impl_915_, 3);
lean_inc(v_l_921_);
v_r_922_ = lean_ctor_get(v_impl_915_, 4);
v___x_923_ = lean_unsigned_to_nat(3u);
v___x_924_ = lean_nat_mul(v___x_923_, v_size_917_);
v___x_925_ = lean_nat_dec_lt(v___x_924_, v_size_918_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
lean_dec(v_l_921_);
v___x_926_ = lean_nat_add(v___x_916_, v_size_917_);
v___x_927_ = lean_nat_add(v___x_926_, v_size_918_);
lean_dec(v___x_926_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_impl_915_);
lean_ctor_set(v___x_772_, 0, v___x_927_);
v___x_929_ = v___x_772_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_l_769_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_impl_915_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_994_; 
lean_inc(v_r_922_);
lean_inc(v_v_920_);
lean_inc(v_k_919_);
lean_inc(v_size_918_);
v_isSharedCheck_994_ = !lean_is_exclusive(v_impl_915_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; 
v_unused_995_ = lean_ctor_get(v_impl_915_, 4);
lean_dec(v_unused_995_);
v_unused_996_ = lean_ctor_get(v_impl_915_, 3);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_impl_915_, 2);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_impl_915_, 1);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_impl_915_, 0);
lean_dec(v_unused_999_);
v___x_932_ = v_impl_915_;
v_isShared_933_ = v_isSharedCheck_994_;
goto v_resetjp_931_;
}
else
{
lean_dec(v_impl_915_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_994_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_size_934_; lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v_l_937_; lean_object* v_r_938_; lean_object* v_size_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_size_934_ = lean_ctor_get(v_l_921_, 0);
v_k_935_ = lean_ctor_get(v_l_921_, 1);
v_v_936_ = lean_ctor_get(v_l_921_, 2);
v_l_937_ = lean_ctor_get(v_l_921_, 3);
v_r_938_ = lean_ctor_get(v_l_921_, 4);
v_size_939_ = lean_ctor_get(v_r_922_, 0);
v___x_940_ = lean_unsigned_to_nat(2u);
v___x_941_ = lean_nat_mul(v___x_940_, v_size_939_);
v___x_942_ = lean_nat_dec_lt(v_size_934_, v___x_941_);
lean_dec(v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_970_; 
lean_inc(v_r_938_);
lean_inc(v_l_937_);
lean_inc(v_v_936_);
lean_inc(v_k_935_);
v_isSharedCheck_970_ = !lean_is_exclusive(v_l_921_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_971_ = lean_ctor_get(v_l_921_, 4);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_l_921_, 3);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_l_921_, 2);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_l_921_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_l_921_, 0);
lean_dec(v_unused_975_);
v___x_944_ = v_l_921_;
v_isShared_945_ = v_isSharedCheck_970_;
goto v_resetjp_943_;
}
else
{
lean_dec(v_l_921_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_970_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_960_; 
v___x_946_ = lean_nat_add(v___x_916_, v_size_917_);
v___x_947_ = lean_nat_add(v___x_946_, v_size_918_);
lean_dec(v_size_918_);
if (lean_obj_tag(v_l_937_) == 0)
{
lean_object* v_size_968_; 
v_size_968_ = lean_ctor_get(v_l_937_, 0);
lean_inc(v_size_968_);
v___y_960_ = v_size_968_;
goto v___jp_959_;
}
else
{
lean_object* v___x_969_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___y_960_ = v___x_969_;
goto v___jp_959_;
}
v___jp_948_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_nat_add(v___y_949_, v___y_951_);
lean_dec(v___y_951_);
lean_dec(v___y_949_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 4, v_r_922_);
lean_ctor_set(v___x_944_, 3, v_r_938_);
lean_ctor_set(v___x_944_, 2, v_v_920_);
lean_ctor_set(v___x_944_, 1, v_k_919_);
lean_ctor_set(v___x_944_, 0, v___x_952_);
v___x_954_ = v___x_944_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_r_938_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_r_922_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 4, v___x_954_);
lean_ctor_set(v___x_932_, 3, v___y_950_);
lean_ctor_set(v___x_932_, 2, v_v_936_);
lean_ctor_set(v___x_932_, 1, v_k_935_);
lean_ctor_set(v___x_932_, 0, v___x_947_);
v___x_956_ = v___x_932_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_k_935_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_v_936_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v___y_950_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
v___jp_959_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_nat_add(v___x_946_, v___y_960_);
lean_dec(v___y_960_);
lean_dec(v___x_946_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_l_937_);
lean_ctor_set(v___x_772_, 0, v___x_961_);
v___x_963_ = v___x_772_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_l_769_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_l_937_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; 
v___x_964_ = lean_nat_add(v___x_916_, v_size_939_);
if (lean_obj_tag(v_r_938_) == 0)
{
lean_object* v_size_965_; 
v_size_965_ = lean_ctor_get(v_r_938_, 0);
lean_inc(v_size_965_);
v___y_949_ = v___x_964_;
v___y_950_ = v___x_963_;
v___y_951_ = v_size_965_;
goto v___jp_948_;
}
else
{
lean_object* v___x_966_; 
v___x_966_ = lean_unsigned_to_nat(0u);
v___y_949_ = v___x_964_;
v___y_950_ = v___x_963_;
v___y_951_ = v___x_966_;
goto v___jp_948_;
}
}
}
}
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
lean_del_object(v___x_772_);
v___x_976_ = lean_nat_add(v___x_916_, v_size_917_);
v___x_977_ = lean_nat_add(v___x_976_, v_size_918_);
lean_dec(v_size_918_);
v___x_978_ = lean_nat_add(v___x_976_, v_size_934_);
lean_dec(v___x_976_);
lean_inc_ref(v_l_769_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 4, v_l_921_);
lean_ctor_set(v___x_932_, 3, v_l_769_);
lean_ctor_set(v___x_932_, 2, v_v_768_);
lean_ctor_set(v___x_932_, 1, v_k_767_);
lean_ctor_set(v___x_932_, 0, v___x_978_);
v___x_980_ = v___x_932_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_l_769_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_l_921_);
v___x_980_ = v_reuseFailAlloc_993_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_isSharedCheck_987_ = !lean_is_exclusive(v_l_769_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; lean_object* v_unused_992_; 
v_unused_988_ = lean_ctor_get(v_l_769_, 4);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_l_769_, 3);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_l_769_, 2);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_l_769_, 1);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_l_769_, 0);
lean_dec(v_unused_992_);
v___x_982_ = v_l_769_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_dec(v_l_769_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 4, v_r_922_);
lean_ctor_set(v___x_982_, 3, v___x_980_);
lean_ctor_set(v___x_982_, 2, v_v_920_);
lean_ctor_set(v___x_982_, 1, v_k_919_);
lean_ctor_set(v___x_982_, 0, v___x_977_);
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_r_922_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1000_; 
v_l_1000_ = lean_ctor_get(v_impl_915_, 3);
lean_inc(v_l_1000_);
if (lean_obj_tag(v_l_1000_) == 0)
{
lean_object* v_r_1001_; lean_object* v_k_1002_; lean_object* v_v_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1026_; 
v_r_1001_ = lean_ctor_get(v_impl_915_, 4);
v_k_1002_ = lean_ctor_get(v_impl_915_, 1);
v_v_1003_ = lean_ctor_get(v_impl_915_, 2);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_impl_915_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; lean_object* v_unused_1028_; 
v_unused_1027_ = lean_ctor_get(v_impl_915_, 3);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_impl_915_, 0);
lean_dec(v_unused_1028_);
v___x_1005_ = v_impl_915_;
v_isShared_1006_ = v_isSharedCheck_1026_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_r_1001_);
lean_inc(v_v_1003_);
lean_inc(v_k_1002_);
lean_dec(v_impl_915_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1026_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_k_1007_; lean_object* v_v_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1022_; 
v_k_1007_ = lean_ctor_get(v_l_1000_, 1);
v_v_1008_ = lean_ctor_get(v_l_1000_, 2);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_l_1000_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; lean_object* v_unused_1024_; lean_object* v_unused_1025_; 
v_unused_1023_ = lean_ctor_get(v_l_1000_, 4);
lean_dec(v_unused_1023_);
v_unused_1024_ = lean_ctor_get(v_l_1000_, 3);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_l_1000_, 0);
lean_dec(v_unused_1025_);
v___x_1010_ = v_l_1000_;
v_isShared_1011_ = v_isSharedCheck_1022_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_v_1008_);
lean_inc(v_k_1007_);
lean_dec(v_l_1000_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1022_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1001_, 2);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 4, v_r_1001_);
lean_ctor_set(v___x_1010_, 3, v_r_1001_);
lean_ctor_set(v___x_1010_, 2, v_v_768_);
lean_ctor_set(v___x_1010_, 1, v_k_767_);
lean_ctor_set(v___x_1010_, 0, v___x_916_);
v___x_1014_ = v___x_1010_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_1021_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_1021_, 3, v_r_1001_);
lean_ctor_set(v_reuseFailAlloc_1021_, 4, v_r_1001_);
v___x_1014_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1016_; 
lean_inc(v_r_1001_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 3, v_r_1001_);
lean_ctor_set(v___x_1005_, 0, v___x_916_);
v___x_1016_ = v___x_1005_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_1002_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_1003_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_r_1001_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_r_1001_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v___x_1016_);
lean_ctor_set(v___x_772_, 3, v___x_1014_);
lean_ctor_set(v___x_772_, 2, v_v_1008_);
lean_ctor_set(v___x_772_, 1, v_k_1007_);
lean_ctor_set(v___x_772_, 0, v___x_1012_);
v___x_1018_ = v___x_772_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_1007_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_1008_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
else
{
lean_object* v_r_1029_; 
v_r_1029_ = lean_ctor_get(v_impl_915_, 4);
lean_inc(v_r_1029_);
if (lean_obj_tag(v_r_1029_) == 0)
{
lean_object* v_k_1030_; lean_object* v_v_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1042_; 
v_k_1030_ = lean_ctor_get(v_impl_915_, 1);
v_v_1031_ = lean_ctor_get(v_impl_915_, 2);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_impl_915_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1043_ = lean_ctor_get(v_impl_915_, 4);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_impl_915_, 3);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_impl_915_, 0);
lean_dec(v_unused_1045_);
v___x_1033_ = v_impl_915_;
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_v_1031_);
lean_inc(v_k_1030_);
lean_dec(v_impl_915_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_unsigned_to_nat(3u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_l_1000_);
lean_ctor_set(v___x_1033_, 2, v_v_768_);
lean_ctor_set(v___x_1033_, 1, v_k_767_);
lean_ctor_set(v___x_1033_, 0, v___x_916_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_l_1000_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_l_1000_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_r_1029_);
lean_ctor_set(v___x_772_, 3, v___x_1037_);
lean_ctor_set(v___x_772_, 2, v_v_1031_);
lean_ctor_set(v___x_772_, 1, v_k_1030_);
lean_ctor_set(v___x_772_, 0, v___x_1035_);
v___x_1039_ = v___x_772_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_1030_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_1031_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_r_1029_);
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
else
{
lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1046_ = lean_unsigned_to_nat(2u);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_impl_915_);
lean_ctor_set(v___x_772_, 3, v_r_1029_);
lean_ctor_set(v___x_772_, 0, v___x_1046_);
v___x_1048_ = v___x_772_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_r_1029_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v_impl_915_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
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
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1u);
v___x_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_k_763_);
lean_ctor_set(v___x_1052_, 2, v_v_764_);
lean_ctor_set(v___x_1052_, 3, v_t_765_);
lean_ctor_set(v___x_1052_, 4, v_t_765_);
return v___x_1052_;
}
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1053_ = lean_box(1);
v___x_1054_ = l_Lake_ExternLib_defaultFacetConfig;
v___x_1055_ = l_Lake_ExternLib_defaultFacet;
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1055_, v___x_1054_, v___x_1053_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__0, &l_Lake_ExternLib_initFacetConfigs___closed__0_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__0);
v___x_1058_ = l_Lake_ExternLib_staticFacetConfig;
v___x_1059_ = l_Lake_ExternLib_staticFacet;
v___x_1060_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1059_, v___x_1058_, v___x_1057_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__1, &l_Lake_ExternLib_initFacetConfigs___closed__1_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__1);
v___x_1062_ = l_Lake_ExternLib_sharedFacetConfig;
v___x_1063_ = l_Lake_ExternLib_sharedFacet;
v___x_1064_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1063_, v___x_1062_, v___x_1061_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1065_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__2, &l_Lake_ExternLib_initFacetConfigs___closed__2_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__2);
v___x_1066_ = l_Lake_ExternLib_dynlibFacetConfig;
v___x_1067_ = l_Lake_ExternLib_dynlibFacet;
v___x_1068_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1067_, v___x_1066_, v___x_1065_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__3, &l_Lake_ExternLib_initFacetConfigs___closed__3_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__3);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_1070_, lean_object* v_k_1071_, lean_object* v_v_1072_, lean_object* v_t_1073_, lean_object* v_hl_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_1071_, v_v_1072_, v_t_1073_);
return v___x_1075_;
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
