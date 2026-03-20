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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_a_47_);
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
lean_inc(v_registeredJobs_71_);
lean_dec_ref(v_a_47_);
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
lean_dec(v_registeredJobs_71_);
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
lean_dec_ref(v_a_47_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___boxed(lean_object* v_lib_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic(v_lib_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
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
lean_object* v_toContext_139_; lean_object* v_lakeEnv_140_; lean_object* v_log_141_; uint8_t v_action_142_; uint8_t v_wantsRebuild_143_; lean_object* v_trace_144_; lean_object* v_buildTime_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_196_; 
v_toContext_139_ = lean_ctor_get(v___y_136_, 1);
lean_inc(v_toContext_139_);
lean_dec_ref(v___y_136_);
v_lakeEnv_140_ = lean_ctor_get(v_toContext_139_, 1);
lean_inc_ref(v_lakeEnv_140_);
lean_dec(v_toContext_139_);
v_log_141_ = lean_ctor_get(v___y_137_, 0);
v_action_142_ = lean_ctor_get_uint8(v___y_137_, sizeof(void*)*3);
v_wantsRebuild_143_ = lean_ctor_get_uint8(v___y_137_, sizeof(void*)*3 + 1);
v_trace_144_ = lean_ctor_get(v___y_137_, 1);
v_buildTime_145_ = lean_ctor_get(v___y_137_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v___y_137_);
if (v_isSharedCheck_196_ == 0)
{
v___x_147_ = v___y_137_;
v_isShared_148_ = v_isSharedCheck_196_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_buildTime_145_);
lean_inc(v_trace_144_);
lean_inc(v_log_141_);
lean_dec(v___y_137_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_196_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v_lean_149_; lean_object* v___y_151_; uint8_t v___x_186_; 
v_lean_149_ = lean_ctor_get(v_lakeEnv_140_, 1);
lean_inc_ref(v_lean_149_);
lean_dec_ref(v_lakeEnv_140_);
v___x_186_ = l_System_Platform_isOSX;
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_187_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__3));
v___x_188_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__4);
v___x_189_ = lean_array_push(v___x_188_, v_staticLib_131_);
v___x_190_ = lean_array_push(v___x_189_, v___x_187_);
v___y_151_ = v___x_190_;
goto v___jp_150_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_191_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__5));
v___x_192_ = lean_string_append(v___x_191_, v_staticLib_131_);
lean_dec_ref(v_staticLib_131_);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_mk_empty_array_with_capacity(v___x_193_);
v___x_195_ = lean_array_push(v___x_194_, v___x_192_);
v___y_151_ = v___x_195_;
goto v___jp_150_;
}
v___jp_150_:
{
lean_object* v_leanLibDir_152_; lean_object* v_cc_153_; lean_object* v_ccLinkSharedFlags_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_leanLibDir_152_ = lean_ctor_get(v_lean_149_, 3);
lean_inc_ref(v_leanLibDir_152_);
v_cc_153_ = lean_ctor_get(v_lean_149_, 13);
lean_inc_ref(v_cc_153_);
v_ccLinkSharedFlags_154_ = lean_ctor_get(v_lean_149_, 19);
lean_inc_ref(v_ccLinkSharedFlags_154_);
lean_dec_ref(v_lean_149_);
v___x_155_ = l_Array_append___redArg(v___y_151_, v_weakArgs_128_);
v___x_156_ = l_Array_append___redArg(v___x_155_, v_traceArgs_129_);
v___x_157_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1, &l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__0___closed__1);
v___x_158_ = lean_array_push(v___x_157_, v_leanLibDir_152_);
v___x_159_ = l_Array_append___redArg(v___x_156_, v___x_158_);
lean_dec_ref(v___x_158_);
v___x_160_ = l_Array_append___redArg(v___x_159_, v_ccLinkSharedFlags_154_);
lean_dec_ref(v_ccLinkSharedFlags_154_);
v___x_161_ = l_Lake_compileSharedLib(v___x_130_, v___x_160_, v_cc_153_, v_log_141_);
lean_dec_ref(v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_173_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_a_163_ = lean_ctor_get(v___x_161_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_173_ == 0)
{
v___x_165_ = v___x_161_;
v_isShared_166_ = v_isSharedCheck_173_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_173_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_a_163_);
v___x_168_ = v___x_147_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_163_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_trace_144_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v_buildTime_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_172_, sizeof(void*)*3, v_action_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_172_, sizeof(void*)*3 + 1, v_wantsRebuild_143_);
v___x_168_ = v_reuseFailAlloc_172_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_170_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_168_);
v___x_170_ = v___x_165_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_162_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_185_; 
v_a_174_ = lean_ctor_get(v___x_161_, 0);
v_a_175_ = lean_ctor_get(v___x_161_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_185_ == 0)
{
v___x_177_ = v___x_161_;
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_inc(v_a_174_);
lean_dec(v___x_161_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_a_175_);
v___x_180_ = v___x_147_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_trace_144_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_buildTime_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*3, v_action_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*3 + 1, v_wantsRebuild_143_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_182_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_180_);
v___x_182_ = v___x_177_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_174_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object* v_weakArgs_197_, lean_object* v_traceArgs_198_, lean_object* v___x_199_, lean_object* v_staticLib_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lake_buildLeanSharedLibOfStatic___lam__0(v_weakArgs_197_, v_traceArgs_198_, v___x_199_, v_staticLib_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_204_);
lean_dec(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec_ref(v_traceArgs_198_);
lean_dec_ref(v_weakArgs_197_);
return v_res_208_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(lean_object* v_as_209_, size_t v_i_210_, size_t v_stop_211_, uint64_t v_b_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = lean_usize_dec_eq(v_i_210_, v_stop_211_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; size_t v___x_219_; size_t v___x_220_; 
v___x_214_ = lean_array_uget_borrowed(v_as_209_, v_i_210_);
v___x_215_ = l_Lake_Hash_nil;
v___x_216_ = lean_string_hash(v___x_214_);
v___x_217_ = lean_uint64_mix_hash(v___x_215_, v___x_216_);
v___x_218_ = lean_uint64_mix_hash(v_b_212_, v___x_217_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_i_210_, v___x_219_);
v_i_210_ = v___x_220_;
v_b_212_ = v___x_218_;
goto _start;
}
else
{
return v_b_212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1___boxed(lean_object* v_as_222_, lean_object* v_i_223_, lean_object* v_stop_224_, lean_object* v_b_225_){
_start:
{
size_t v_i_boxed_226_; size_t v_stop_boxed_227_; uint64_t v_b_boxed_228_; uint64_t v_res_229_; lean_object* v_r_230_; 
v_i_boxed_226_ = lean_unbox_usize(v_i_223_);
lean_dec(v_i_223_);
v_stop_boxed_227_ = lean_unbox_usize(v_stop_224_);
lean_dec(v_stop_224_);
v_b_boxed_228_ = lean_unbox_uint64(v_b_225_);
lean_dec_ref(v_b_225_);
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_as_222_, v_i_boxed_226_, v_stop_boxed_227_, v_b_boxed_228_);
lean_dec_ref(v_as_222_);
v_r_230_ = lean_box_uint64(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
if (lean_obj_tag(v_x_233_) == 0)
{
return v_x_232_;
}
else
{
lean_object* v_head_234_; lean_object* v_tail_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_head_234_ = lean_ctor_get(v_x_233_, 0);
v_tail_235_ = lean_ctor_get(v_x_233_, 1);
v___x_236_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___closed__0));
v___x_237_ = lean_string_append(v_x_232_, v___x_236_);
v___x_238_ = lean_string_append(v___x_237_, v_head_234_);
v_x_232_ = v___x_238_;
v_x_233_ = v_tail_235_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0___boxed(lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v_x_240_, v_x_241_);
lean_dec(v_x_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v___x_247_; 
v___x_247_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__0));
return v___x_247_;
}
else
{
lean_object* v_tail_248_; 
v_tail_248_ = lean_ctor_get(v_x_246_, 1);
if (lean_obj_tag(v_tail_248_) == 0)
{
lean_object* v_head_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_head_249_ = lean_ctor_get(v_x_246_, 0);
v___x_250_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_251_ = lean_string_append(v___x_250_, v_head_249_);
v___x_252_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__2));
v___x_253_ = lean_string_append(v___x_251_, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v_head_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint32_t v___x_258_; lean_object* v___x_259_; 
v_head_254_ = lean_ctor_get(v_x_246_, 0);
v___x_255_ = ((lean_object*)(l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___closed__1));
v___x_256_ = lean_string_append(v___x_255_, v_head_254_);
v___x_257_ = l_List_foldl___at___00List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0_spec__0(v___x_256_, v_tail_248_);
v___x_258_ = 93;
v___x_259_ = lean_string_push(v___x_257_, v___x_258_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0___boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v_x_260_);
lean_dec(v_x_260_);
return v_res_261_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_nat_to_int(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4(void){
_start:
{
uint32_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = 0;
v___x_269_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__3);
v___x_270_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set_uint32(v___x_270_, sizeof(void*)*1, v___x_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object* v_traceArgs_271_, lean_object* v_weakArgs_272_, lean_object* v_staticLib_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_log_281_; uint8_t v_action_282_; uint8_t v_wantsRebuild_283_; lean_object* v_trace_284_; lean_object* v_buildTime_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_342_; 
v_log_281_ = lean_ctor_get(v___y_279_, 0);
v_action_282_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3);
v_wantsRebuild_283_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 1);
v_trace_284_ = lean_ctor_get(v___y_279_, 1);
v_buildTime_285_ = lean_ctor_get(v___y_279_, 2);
v_isSharedCheck_342_ = !lean_is_exclusive(v___y_279_);
if (v_isSharedCheck_342_ == 0)
{
v___x_287_ = v___y_279_;
v_isShared_288_ = v_isSharedCheck_342_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_buildTime_285_);
lean_inc(v_trace_284_);
lean_inc(v_log_281_);
lean_dec(v___y_279_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_342_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_leanTrace_289_; lean_object* v___x_290_; uint64_t v___y_292_; uint64_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_leanTrace_289_ = lean_ctor_get(v___y_278_, 2);
lean_inc_ref(v_leanTrace_289_);
v___x_290_ = l_Lake_BuildTrace_mix(v_trace_284_, v_leanTrace_289_);
v___x_331_ = l_Lake_Hash_nil;
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_array_get_size(v_traceArgs_271_);
v___x_334_ = lean_nat_dec_lt(v___x_332_, v___x_333_);
if (v___x_334_ == 0)
{
v___y_292_ = v___x_331_;
goto v___jp_291_;
}
else
{
uint8_t v___x_335_; 
v___x_335_ = lean_nat_dec_le(v___x_333_, v___x_333_);
if (v___x_335_ == 0)
{
if (v___x_334_ == 0)
{
v___y_292_ = v___x_331_;
goto v___jp_291_;
}
else
{
size_t v___x_336_; size_t v___x_337_; uint64_t v___x_338_; 
v___x_336_ = ((size_t)0ULL);
v___x_337_ = lean_usize_of_nat(v___x_333_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_271_, v___x_336_, v___x_337_, v___x_331_);
v___y_292_ = v___x_338_;
goto v___jp_291_;
}
}
else
{
size_t v___x_339_; size_t v___x_340_; uint64_t v___x_341_; 
v___x_339_ = ((size_t)0ULL);
v___x_340_ = lean_usize_of_nat(v___x_333_);
v___x_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_buildLeanSharedLibOfStatic_spec__1(v_traceArgs_271_, v___x_339_, v___x_340_, v___x_331_);
v___y_292_ = v___x_341_;
goto v___jp_291_;
}
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_293_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__0));
v___x_294_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__1));
lean_inc_ref(v_traceArgs_271_);
v___x_295_ = lean_array_to_list(v_traceArgs_271_);
v___x_296_ = l_List_toString___at___00Lake_buildLeanSharedLibOfStatic_spec__0(v___x_295_);
lean_dec(v___x_295_);
v___x_297_ = lean_string_append(v___x_294_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = lean_string_append(v___x_293_, v___x_297_);
lean_dec_ref(v___x_297_);
v___x_299_ = ((lean_object*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__2));
v___x_300_ = lean_obj_once(&l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4, &l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4_once, _init_l_Lake_buildLeanSharedLibOfStatic___lam__1___closed__4);
v___x_301_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
lean_ctor_set(v___x_301_, 2, v___x_300_);
lean_ctor_set_uint64(v___x_301_, sizeof(void*)*3, v___y_292_);
v___x_302_ = l_Lake_BuildTrace_mix(v___x_290_, v___x_301_);
v___x_303_ = l_Lake_platformTrace;
v___x_304_ = l_Lake_BuildTrace_mix(v___x_302_, v___x_303_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_304_);
v___x_306_ = v___x_287_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_log_281_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_buildTime_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*3, v_action_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_330_, sizeof(void*)*3 + 1, v_wantsRebuild_283_);
v___x_306_ = v_reuseFailAlloc_330_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___f_309_; uint8_t v___x_310_; lean_object* v___x_311_; 
v___x_307_ = l_Lake_sharedLibExt;
lean_inc_ref(v_staticLib_273_);
v___x_308_ = l_System_FilePath_withExtension(v_staticLib_273_, v___x_307_);
lean_inc_ref(v___x_308_);
v___f_309_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed), 11, 4);
lean_closure_set(v___f_309_, 0, v_weakArgs_272_);
lean_closure_set(v___f_309_, 1, v_traceArgs_271_);
lean_closure_set(v___f_309_, 2, v___x_308_);
lean_closure_set(v___f_309_, 3, v_staticLib_273_);
v___x_310_ = 0;
lean_inc_ref(v___x_308_);
v___x_311_ = l_Lake_buildFileUnlessUpToDate_x27(v___x_308_, v___f_309_, v___x_310_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___x_306_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_a_312_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v___x_311_, 0);
lean_dec(v_unused_320_);
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_308_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v___x_308_);
v_a_321_ = lean_ctor_get(v___x_311_, 0);
v_a_322_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_311_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_inc(v_a_321_);
lean_dec(v___x_311_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_321_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed(lean_object* v_traceArgs_343_, lean_object* v_weakArgs_344_, lean_object* v_staticLib_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lake_buildLeanSharedLibOfStatic___lam__1(v_traceArgs_343_, v_weakArgs_344_, v_staticLib_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* v_staticLibJob_354_, lean_object* v_weakArgs_355_, lean_object* v_traceArgs_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; 
v___f_364_ = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__1___boxed), 10, 2);
lean_closure_set(v___f_364_, 0, v_traceArgs_356_);
lean_closure_set(v___f_364_, 1, v_weakArgs_355_);
v___x_365_ = l_Lake_instDataKindFilePath;
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = 0;
v___x_368_ = l_Lake_Job_mapM___redArg(v___x_365_, v_staticLibJob_354_, v___f_364_, v___x_366_, v___x_367_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___boxed(lean_object* v_staticLibJob_369_, lean_object* v_weakArgs_370_, lean_object* v_traceArgs_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lake_buildLeanSharedLibOfStatic(v_staticLibJob_369_, v_weakArgs_370_, v_traceArgs_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
return v_res_379_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__1));
v___x_384_ = l_Lake_BuildTrace_nil(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(lean_object* v___x_385_, lean_object* v_config_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
lean_inc_ref(v___y_387_);
lean_inc_ref(v___y_391_);
lean_inc(v___y_390_);
lean_inc(v___y_389_);
lean_inc(v___y_388_);
v___x_394_ = lean_apply_7(v___y_387_, v___x_385_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, lean_box(0));
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_toLeanConfig_395_; lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_408_; 
v_toLeanConfig_395_ = lean_ctor_get(v_config_386_, 1);
lean_inc_ref(v_toLeanConfig_395_);
lean_dec_ref(v_config_386_);
v_a_396_ = lean_ctor_get(v___x_394_, 0);
v_a_397_ = lean_ctor_get(v___x_394_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_408_ == 0)
{
v___x_399_ = v___x_394_;
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_inc(v_a_396_);
lean_dec(v___x_394_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_moreLinkArgs_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v_moreLinkArgs_401_ = lean_ctor_get(v_toLeanConfig_395_, 8);
lean_inc_ref(v_moreLinkArgs_401_);
lean_dec_ref(v_toLeanConfig_395_);
v___x_402_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__0));
v___x_403_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_404_ = l_Lake_buildLeanSharedLibOfStatic(v_a_396_, v_moreLinkArgs_401_, v___x_402_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___x_403_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_404_);
v___x_406_ = v___x_399_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_397_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec_ref(v_config_386_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed(lean_object* v___x_409_, lean_object* v_config_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0(v___x_409_, v_config_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(lean_object* v_lib_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_pkg_428_; lean_object* v_name_429_; lean_object* v_keyName_430_; lean_object* v_config_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___f_437_; lean_object* v___x_438_; 
v_pkg_428_ = lean_ctor_get(v_lib_420_, 0);
v_name_429_ = lean_ctor_get(v_lib_420_, 1);
lean_inc(v_name_429_);
v_keyName_430_ = lean_ctor_get(v_pkg_428_, 2);
v_config_431_ = lean_ctor_get(v_pkg_428_, 6);
lean_inc_ref(v_config_431_);
v___x_432_ = l_Lake_instDataKindFilePath;
v___x_433_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_429_);
lean_inc(v_keyName_430_);
v___x_434_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_434_, 0, v_keyName_430_);
lean_ctor_set(v___x_434_, 1, v_name_429_);
v___x_435_ = l_Lake_ExternLib_keyword;
v___x_436_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_436_, 0, v___x_434_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
lean_ctor_set(v___x_436_, 2, v_lib_420_);
lean_ctor_set(v___x_436_, 3, v___x_433_);
v___f_437_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___boxed), 9, 2);
lean_closure_set(v___f_437_, 0, v___x_436_);
lean_closure_set(v___f_437_, 1, v_config_431_);
lean_inc_ref(v_a_425_);
v___x_438_ = l_Lake_ensureJob___redArg(v___x_432_, v___f_437_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_470_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_a_440_ = lean_ctor_get(v___x_438_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_470_ == 0)
{
v___x_442_ = v___x_438_;
v_isShared_443_ = v_isSharedCheck_470_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_470_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_task_444_; lean_object* v_kind_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_468_; 
v_task_444_ = lean_ctor_get(v_a_439_, 0);
v_kind_445_ = lean_ctor_get(v_a_439_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v_a_439_, 2);
lean_dec(v_unused_469_);
v___x_447_ = v_a_439_;
v_isShared_448_ = v_isSharedCheck_468_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_kind_445_);
lean_inc(v_task_444_);
lean_dec(v_a_439_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_468_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_registeredJobs_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v_job_459_; 
v_registeredJobs_449_ = lean_ctor_get(v_a_425_, 3);
lean_inc(v_registeredJobs_449_);
lean_dec_ref(v_a_425_);
v___x_450_ = lean_st_ref_take(v_registeredJobs_449_);
v___x_451_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_452_ = l_Lean_Name_str___override(v_name_429_, v___x_451_);
v___x_453_ = 1;
v___x_454_ = l_Lean_Name_toString(v___x_452_, v___x_453_);
v___x_455_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___closed__0));
v___x_456_ = lean_string_append(v___x_454_, v___x_455_);
v___x_457_ = 0;
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 2, v___x_456_);
v_job_459_ = v___x_447_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_task_444_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_kind_445_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v___x_456_);
v_job_459_ = v_reuseFailAlloc_467_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
lean_ctor_set_uint8(v_job_459_, sizeof(void*)*3, v___x_457_);
lean_inc_ref(v_job_459_);
v___x_460_ = l_Lake_Job_toOpaque___redArg(v_job_459_);
v___x_461_ = lean_array_push(v___x_450_, v___x_460_);
v___x_462_ = lean_st_ref_set(v_registeredJobs_449_, v___x_461_);
lean_dec(v_registeredJobs_449_);
v___x_463_ = l_Lake_Job_renew___redArg(v_job_459_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_463_);
v___x_465_ = v___x_442_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_a_440_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
else
{
lean_dec(v_name_429_);
lean_dec_ref(v_a_425_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___boxed(lean_object* v_lib_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared(v_lib_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v_res_479_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___f_481_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_482_ = 1;
v___x_483_ = l_Lake_instDataKindFilePath;
v___x_484_ = ((lean_object*)(l_Lake_ExternLib_sharedFacetConfig___closed__0));
v___x_485_ = l_Lake_ExternLib_keyword;
v___x_486_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_483_);
lean_ctor_set(v___x_486_, 3, v___f_481_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*4, v___x_482_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*4 + 1, v___x_482_);
return v___x_486_;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Lake_ExternLib_sharedFacetConfig___closed__1, &l_Lake_ExternLib_sharedFacetConfig___closed__1_once, _init_l_Lake_ExternLib_sharedFacetConfig___closed__1);
return v___x_487_;
}
}
static lean_object* _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3));
v___x_494_ = lean_string_utf8_byte_size(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(lean_object* v_sharedLib_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
lean_inc_ref(v_sharedLib_496_);
v___x_504_ = l_System_FilePath_fileStem(v_sharedLib_496_);
if (lean_obj_tag(v___x_504_) == 1)
{
lean_object* v_val_505_; uint8_t v___x_506_; uint8_t v___y_508_; 
v_val_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_val_505_);
lean_dec_ref(v___x_504_);
v___x_506_ = l_System_Platform_isWindows;
if (v___x_506_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_539_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__3));
v___x_540_ = lean_string_utf8_byte_size(v_val_505_);
v___x_541_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4, &l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4_once, _init_l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__4);
v___x_542_ = lean_nat_dec_le(v___x_541_, v___x_540_);
if (v___x_542_ == 0)
{
v___y_508_ = v___x_506_;
goto v___jp_507_;
}
else
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_string_memcmp(v_val_505_, v___x_539_, v___x_543_, v___x_543_, v___x_541_);
v___y_508_ = v___x_544_;
goto v___jp_507_;
}
}
else
{
uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_545_ = 0;
v___x_546_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_547_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_547_, 0, v_sharedLib_496_);
lean_ctor_set(v___x_547_, 1, v_val_505_);
lean_ctor_set(v___x_547_, 2, v___x_546_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*3, v___x_545_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___y_502_);
return v___x_548_;
}
v___jp_507_:
{
if (v___y_508_ == 0)
{
lean_object* v_log_509_; uint8_t v_action_510_; uint8_t v_wantsRebuild_511_; lean_object* v_trace_512_; lean_object* v_buildTime_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_val_505_);
v_log_509_ = lean_ctor_get(v___y_502_, 0);
v_action_510_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*3);
v_wantsRebuild_511_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*3 + 1);
v_trace_512_ = lean_ctor_get(v___y_502_, 1);
v_buildTime_513_ = lean_ctor_get(v___y_502_, 2);
v_isSharedCheck_529_ = !lean_is_exclusive(v___y_502_);
if (v_isSharedCheck_529_ == 0)
{
v___x_515_ = v___y_502_;
v_isShared_516_ = v_isSharedCheck_529_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_buildTime_513_);
lean_inc(v_trace_512_);
lean_inc(v_log_509_);
lean_dec(v___y_502_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_529_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_517_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_518_ = lean_string_append(v___x_517_, v_sharedLib_496_);
lean_dec_ref(v_sharedLib_496_);
v___x_519_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__1));
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
v___x_521_ = 3;
v___x_522_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_521_);
v___x_523_ = lean_array_get_size(v_log_509_);
v___x_524_ = lean_array_push(v_log_509_, v___x_522_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_524_);
v___x_526_ = v___x_515_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_trace_512_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_buildTime_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*3, v_action_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_528_, sizeof(void*)*3 + 1, v_wantsRebuild_511_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_523_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
return v___x_527_;
}
}
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_530_ = lean_unsigned_to_nat(3u);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_string_utf8_byte_size(v_val_505_);
lean_inc(v_val_505_);
v___x_533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_533_, 0, v_val_505_);
lean_ctor_set(v___x_533_, 1, v___x_531_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = l_String_Slice_Pos_nextn(v___x_533_, v___x_531_, v___x_530_);
lean_dec_ref(v___x_533_);
v___x_535_ = lean_string_utf8_extract(v_val_505_, v___x_534_, v___x_532_);
lean_dec(v___x_534_);
lean_dec(v_val_505_);
v___x_536_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__2));
v___x_537_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_537_, 0, v_sharedLib_496_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_536_);
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*3, v___x_506_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___y_502_);
return v___x_538_;
}
}
}
else
{
lean_object* v_log_549_; uint8_t v_action_550_; uint8_t v_wantsRebuild_551_; lean_object* v_trace_552_; lean_object* v_buildTime_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_569_; 
lean_dec(v___x_504_);
v_log_549_ = lean_ctor_get(v___y_502_, 0);
v_action_550_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*3);
v_wantsRebuild_551_ = lean_ctor_get_uint8(v___y_502_, sizeof(void*)*3 + 1);
v_trace_552_ = lean_ctor_get(v___y_502_, 1);
v_buildTime_553_ = lean_ctor_get(v___y_502_, 2);
v_isSharedCheck_569_ = !lean_is_exclusive(v___y_502_);
if (v_isSharedCheck_569_ == 0)
{
v___x_555_ = v___y_502_;
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_buildTime_553_);
lean_inc(v_trace_552_);
lean_inc(v_log_549_);
lean_dec(v___y_502_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_569_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_557_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__0));
v___x_558_ = lean_string_append(v___x_557_, v_sharedLib_496_);
lean_dec_ref(v_sharedLib_496_);
v___x_559_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___closed__5));
v___x_560_ = lean_string_append(v___x_558_, v___x_559_);
v___x_561_ = 3;
v___x_562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*1, v___x_561_);
v___x_563_ = lean_array_get_size(v_log_549_);
v___x_564_ = lean_array_push(v_log_549_, v___x_562_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_564_);
v___x_566_ = v___x_555_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_trace_552_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_buildTime_553_);
lean_ctor_set_uint8(v_reuseFailAlloc_568_, sizeof(void*)*3, v_action_550_);
lean_ctor_set_uint8(v_reuseFailAlloc_568_, sizeof(void*)*3 + 1, v_wantsRebuild_551_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; 
v___x_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0___boxed(lean_object* v_sharedLib_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___lam__0(v_sharedLib_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(lean_object* v_sharedLibTarget_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; 
v___f_588_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___closed__0));
v___x_589_ = l_Lake_instDataKindDynlib;
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = 0;
v___x_592_ = l_Lake_Job_mapM___redArg(v___x_589_, v_sharedLibTarget_580_, v___f_588_, v___x_590_, v___x_591_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared___boxed(lean_object* v_sharedLibTarget_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_sharedLibTarget_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(lean_object* v___x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
lean_inc_ref(v___y_603_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc(v___y_605_);
lean_inc(v___y_604_);
v___x_610_ = lean_apply_7(v___y_603_, v___x_602_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_621_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_a_612_ = lean_ctor_get(v___x_610_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_621_ == 0)
{
v___x_614_ = v___x_610_;
v_isShared_615_ = v_isSharedCheck_621_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_621_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = lean_obj_once(&l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2, &l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2_once, _init_l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildShared___lam__0___closed__2);
v___x_617_ = l___private_Lake_Build_ExternLib_0__Lake_computeDynlibOfShared(v_a_611_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___x_616_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_617_);
v___x_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_a_612_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
lean_object* v_a_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
v_a_622_ = lean_ctor_get(v___x_610_, 0);
v_a_623_ = lean_ctor_get(v___x_610_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_610_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_inc(v_a_622_);
lean_dec(v___x_610_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed(lean_object* v___x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0(v___x_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(lean_object* v_lib_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_pkg_649_; lean_object* v_name_650_; lean_object* v_keyName_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; 
v_pkg_649_ = lean_ctor_get(v_lib_641_, 0);
v_name_650_ = lean_ctor_get(v_lib_641_, 1);
lean_inc(v_name_650_);
v_keyName_651_ = lean_ctor_get(v_pkg_649_, 2);
v___x_652_ = l_Lake_instDataKindDynlib;
v___x_653_ = l_Lake_ExternLib_sharedFacet;
lean_inc(v_name_650_);
lean_inc(v_keyName_651_);
v___x_654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_654_, 0, v_keyName_651_);
lean_ctor_set(v___x_654_, 1, v_name_650_);
v___x_655_ = l_Lake_ExternLib_keyword;
v___x_656_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_ctor_set(v___x_656_, 2, v_lib_641_);
lean_ctor_set(v___x_656_, 3, v___x_653_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___lam__0___boxed), 8, 1);
lean_closure_set(v___f_657_, 0, v___x_656_);
lean_inc_ref(v_a_646_);
v___x_658_ = l_Lake_ensureJob___redArg(v___x_652_, v___f_657_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_690_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_a_660_ = lean_ctor_get(v___x_658_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_690_ == 0)
{
v___x_662_ = v___x_658_;
v_isShared_663_ = v_isSharedCheck_690_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_690_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_task_664_; lean_object* v_kind_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_688_; 
v_task_664_ = lean_ctor_get(v_a_659_, 0);
v_kind_665_ = lean_ctor_get(v_a_659_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v_a_659_, 2);
lean_dec(v_unused_689_);
v___x_667_ = v_a_659_;
v_isShared_668_ = v_isSharedCheck_688_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_kind_665_);
lean_inc(v_task_664_);
lean_dec(v_a_659_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_688_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_registeredJobs_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v_job_679_; 
v_registeredJobs_669_ = lean_ctor_get(v_a_646_, 3);
lean_inc(v_registeredJobs_669_);
lean_dec_ref(v_a_646_);
v___x_670_ = lean_st_ref_take(v_registeredJobs_669_);
v___x_671_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildStatic___closed__0));
v___x_672_ = l_Lean_Name_str___override(v_name_650_, v___x_671_);
v___x_673_ = 1;
v___x_674_ = l_Lean_Name_toString(v___x_672_, v___x_673_);
v___x_675_ = ((lean_object*)(l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___closed__0));
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
v___x_677_ = 0;
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 2, v___x_676_);
v_job_679_ = v___x_667_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_task_664_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_kind_665_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v___x_676_);
v_job_679_ = v_reuseFailAlloc_687_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
lean_ctor_set_uint8(v_job_679_, sizeof(void*)*3, v___x_677_);
lean_inc_ref(v_job_679_);
v___x_680_ = l_Lake_Job_toOpaque___redArg(v_job_679_);
v___x_681_ = lean_array_push(v___x_670_, v___x_680_);
v___x_682_ = lean_st_ref_set(v_registeredJobs_669_, v___x_681_);
lean_dec(v_registeredJobs_669_);
v___x_683_ = l_Lake_Job_renew___redArg(v_job_679_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_683_);
v___x_685_ = v___x_662_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_a_660_);
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
else
{
lean_dec(v_name_650_);
lean_dec_ref(v_a_646_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib___boxed(lean_object* v_lib_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recComputeDynlib(v_lib_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t v_fmt_700_, lean_object* v_a_701_){
_start:
{
if (v_fmt_700_ == 0)
{
lean_object* v_path_702_; 
v_path_702_ = lean_ctor_get(v_a_701_, 0);
lean_inc_ref(v_path_702_);
return v_path_702_;
}
else
{
lean_object* v_path_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_path_703_ = lean_ctor_get(v_a_701_, 0);
lean_inc_ref(v_path_703_);
v___x_704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_704_, 0, v_path_703_);
v___x_705_ = l_Lean_Json_compress(v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object* v_fmt_706_, lean_object* v_a_707_){
_start:
{
uint8_t v_fmt_boxed_708_; lean_object* v_res_709_; 
v_fmt_boxed_708_ = lean_unbox(v_fmt_706_);
v_res_709_ = l_Lake_formatQuery___at___00Lake_ExternLib_dynlibFacetConfig_spec__0(v_fmt_boxed_708_, v_a_707_);
lean_dec_ref(v_a_707_);
return v_res_709_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___f_712_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__0));
v___x_713_ = 1;
v___x_714_ = l_Lake_instDataKindDynlib;
v___x_715_ = ((lean_object*)(l_Lake_ExternLib_dynlibFacetConfig___closed__1));
v___x_716_ = l_Lake_ExternLib_keyword;
v___x_717_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_715_);
lean_ctor_set(v___x_717_, 2, v___x_714_);
lean_ctor_set(v___x_717_, 3, v___f_712_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*4, v___x_713_);
lean_ctor_set_uint8(v___x_717_, sizeof(void*)*4 + 1, v___x_713_);
return v___x_717_;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Lake_ExternLib_dynlibFacetConfig___closed__2, &l_Lake_ExternLib_dynlibFacetConfig___closed__2_once, _init_l_Lake_ExternLib_dynlibFacetConfig___closed__2);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(lean_object* v_lib_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_pkg_727_; lean_object* v_name_728_; lean_object* v_keyName_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_pkg_727_ = lean_ctor_get(v_lib_719_, 0);
v_name_728_ = lean_ctor_get(v_lib_719_, 1);
v_keyName_729_ = lean_ctor_get(v_pkg_727_, 2);
v___x_730_ = l_Lake_ExternLib_staticFacet;
lean_inc(v_name_728_);
lean_inc(v_keyName_729_);
v___x_731_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_731_, 0, v_keyName_729_);
lean_ctor_set(v___x_731_, 1, v_name_728_);
v___x_732_ = l_Lake_ExternLib_keyword;
v___x_733_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_ctor_set(v___x_733_, 2, v_lib_719_);
lean_ctor_set(v___x_733_, 3, v___x_730_);
v___x_734_ = lean_apply_7(v_a_720_, v___x_733_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, lean_box(0));
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault___boxed(lean_object* v_lib_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lake_Build_ExternLib_0__Lake_ExternLib_recBuildDefault(v_lib_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_);
return v_res_743_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_745_; lean_object* v___f_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_745_ = 0;
v___f_746_ = ((lean_object*)(l_Lake_ExternLib_staticFacetConfig___closed__0));
v___x_747_ = 1;
v___x_748_ = l_Lake_instDataKindFilePath;
v___x_749_ = ((lean_object*)(l_Lake_ExternLib_defaultFacetConfig___closed__0));
v___x_750_ = l_Lake_ExternLib_keyword;
v___x_751_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
lean_ctor_set(v___x_751_, 2, v___x_748_);
lean_ctor_set(v___x_751_, 3, v___f_746_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*4, v___x_747_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*4 + 1, v___x_745_);
return v___x_751_;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lake_ExternLib_defaultFacetConfig___closed__1, &l_Lake_ExternLib_defaultFacetConfig___closed__1_once, _init_l_Lake_ExternLib_defaultFacetConfig___closed__1);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_753_, lean_object* v_v_754_, lean_object* v_t_755_){
_start:
{
if (lean_obj_tag(v_t_755_) == 0)
{
lean_object* v_size_756_; lean_object* v_k_757_; lean_object* v_v_758_; lean_object* v_l_759_; lean_object* v_r_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_1040_; 
v_size_756_ = lean_ctor_get(v_t_755_, 0);
v_k_757_ = lean_ctor_get(v_t_755_, 1);
v_v_758_ = lean_ctor_get(v_t_755_, 2);
v_l_759_ = lean_ctor_get(v_t_755_, 3);
v_r_760_ = lean_ctor_get(v_t_755_, 4);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_t_755_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_762_ = v_t_755_;
v_isShared_763_ = v_isSharedCheck_1040_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_r_760_);
lean_inc(v_l_759_);
lean_inc(v_v_758_);
lean_inc(v_k_757_);
lean_inc(v_size_756_);
lean_dec(v_t_755_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_1040_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; 
v___x_764_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_753_, v_k_757_);
switch(v___x_764_)
{
case 0:
{
lean_object* v_impl_765_; lean_object* v___x_766_; 
lean_dec(v_size_756_);
v_impl_765_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_753_, v_v_754_, v_l_759_);
v___x_766_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_760_) == 0)
{
lean_object* v_size_767_; lean_object* v_size_768_; lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v_l_771_; lean_object* v_r_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_size_767_ = lean_ctor_get(v_r_760_, 0);
v_size_768_ = lean_ctor_get(v_impl_765_, 0);
lean_inc(v_size_768_);
v_k_769_ = lean_ctor_get(v_impl_765_, 1);
lean_inc(v_k_769_);
v_v_770_ = lean_ctor_get(v_impl_765_, 2);
lean_inc(v_v_770_);
v_l_771_ = lean_ctor_get(v_impl_765_, 3);
lean_inc(v_l_771_);
v_r_772_ = lean_ctor_get(v_impl_765_, 4);
lean_inc(v_r_772_);
v___x_773_ = lean_unsigned_to_nat(3u);
v___x_774_ = lean_nat_mul(v___x_773_, v_size_767_);
v___x_775_ = lean_nat_dec_lt(v___x_774_, v_size_768_);
lean_dec(v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v_r_772_);
lean_dec(v_l_771_);
lean_dec(v_v_770_);
lean_dec(v_k_769_);
v___x_776_ = lean_nat_add(v___x_766_, v_size_768_);
lean_dec(v_size_768_);
v___x_777_ = lean_nat_add(v___x_776_, v_size_767_);
lean_dec(v___x_776_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 3, v_impl_765_);
lean_ctor_set(v___x_762_, 0, v___x_777_);
v___x_779_ = v___x_762_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_impl_765_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_r_760_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_846_; 
v_isSharedCheck_846_ = !lean_is_exclusive(v_impl_765_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; lean_object* v_unused_851_; 
v_unused_847_ = lean_ctor_get(v_impl_765_, 4);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_impl_765_, 3);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_impl_765_, 2);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_impl_765_, 1);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_impl_765_, 0);
lean_dec(v_unused_851_);
v___x_782_ = v_impl_765_;
v_isShared_783_ = v_isSharedCheck_846_;
goto v_resetjp_781_;
}
else
{
lean_dec(v_impl_765_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_846_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_size_784_; lean_object* v_size_785_; lean_object* v_k_786_; lean_object* v_v_787_; lean_object* v_l_788_; lean_object* v_r_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_size_784_ = lean_ctor_get(v_l_771_, 0);
v_size_785_ = lean_ctor_get(v_r_772_, 0);
v_k_786_ = lean_ctor_get(v_r_772_, 1);
v_v_787_ = lean_ctor_get(v_r_772_, 2);
v_l_788_ = lean_ctor_get(v_r_772_, 3);
v_r_789_ = lean_ctor_get(v_r_772_, 4);
v___x_790_ = lean_unsigned_to_nat(2u);
v___x_791_ = lean_nat_mul(v___x_790_, v_size_784_);
v___x_792_ = lean_nat_dec_lt(v_size_785_, v___x_791_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_821_; 
lean_inc(v_r_789_);
lean_inc(v_l_788_);
lean_inc(v_v_787_);
lean_inc(v_k_786_);
v_isSharedCheck_821_ = !lean_is_exclusive(v_r_772_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; lean_object* v_unused_823_; lean_object* v_unused_824_; lean_object* v_unused_825_; lean_object* v_unused_826_; 
v_unused_822_ = lean_ctor_get(v_r_772_, 4);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_r_772_, 3);
lean_dec(v_unused_823_);
v_unused_824_ = lean_ctor_get(v_r_772_, 2);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_r_772_, 1);
lean_dec(v_unused_825_);
v_unused_826_ = lean_ctor_get(v_r_772_, 0);
lean_dec(v_unused_826_);
v___x_794_ = v_r_772_;
v_isShared_795_ = v_isSharedCheck_821_;
goto v_resetjp_793_;
}
else
{
lean_dec(v_r_772_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_821_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___x_809_; lean_object* v___y_811_; 
v___x_796_ = lean_nat_add(v___x_766_, v_size_768_);
lean_dec(v_size_768_);
v___x_797_ = lean_nat_add(v___x_796_, v_size_767_);
lean_dec(v___x_796_);
v___x_809_ = lean_nat_add(v___x_766_, v_size_784_);
if (lean_obj_tag(v_l_788_) == 0)
{
lean_object* v_size_819_; 
v_size_819_ = lean_ctor_get(v_l_788_, 0);
lean_inc(v_size_819_);
v___y_811_ = v_size_819_;
goto v___jp_810_;
}
else
{
lean_object* v___x_820_; 
v___x_820_ = lean_unsigned_to_nat(0u);
v___y_811_ = v___x_820_;
goto v___jp_810_;
}
v___jp_798_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_nat_add(v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec(v___y_800_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 4, v_r_760_);
lean_ctor_set(v___x_794_, 3, v_r_789_);
lean_ctor_set(v___x_794_, 2, v_v_758_);
lean_ctor_set(v___x_794_, 1, v_k_757_);
lean_ctor_set(v___x_794_, 0, v___x_802_);
v___x_804_ = v___x_794_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_r_789_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_r_760_);
v___x_804_ = v_reuseFailAlloc_808_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v___x_804_);
lean_ctor_set(v___x_782_, 3, v___y_799_);
lean_ctor_set(v___x_782_, 2, v_v_787_);
lean_ctor_set(v___x_782_, 1, v_k_786_);
lean_ctor_set(v___x_782_, 0, v___x_797_);
v___x_806_ = v___x_782_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_786_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_787_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v___y_799_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
v___jp_810_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_nat_add(v___x_809_, v___y_811_);
lean_dec(v___y_811_);
lean_dec(v___x_809_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v_l_788_);
lean_ctor_set(v___x_762_, 3, v_l_771_);
lean_ctor_set(v___x_762_, 2, v_v_770_);
lean_ctor_set(v___x_762_, 1, v_k_769_);
lean_ctor_set(v___x_762_, 0, v___x_812_);
v___x_814_ = v___x_762_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_l_771_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_l_788_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_nat_add(v___x_766_, v_size_767_);
if (lean_obj_tag(v_r_789_) == 0)
{
lean_object* v_size_816_; 
v_size_816_ = lean_ctor_get(v_r_789_, 0);
lean_inc(v_size_816_);
v___y_799_ = v___x_814_;
v___y_800_ = v___x_815_;
v___y_801_ = v_size_816_;
goto v___jp_798_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = lean_unsigned_to_nat(0u);
v___y_799_ = v___x_814_;
v___y_800_ = v___x_815_;
v___y_801_ = v___x_817_;
goto v___jp_798_;
}
}
}
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
lean_del_object(v___x_762_);
v___x_827_ = lean_nat_add(v___x_766_, v_size_768_);
lean_dec(v_size_768_);
v___x_828_ = lean_nat_add(v___x_827_, v_size_767_);
lean_dec(v___x_827_);
v___x_829_ = lean_nat_add(v___x_766_, v_size_767_);
v___x_830_ = lean_nat_add(v___x_829_, v_size_785_);
lean_dec(v___x_829_);
lean_inc_ref(v_r_760_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v_r_760_);
lean_ctor_set(v___x_782_, 3, v_r_772_);
lean_ctor_set(v___x_782_, 2, v_v_758_);
lean_ctor_set(v___x_782_, 1, v_k_757_);
lean_ctor_set(v___x_782_, 0, v___x_830_);
v___x_832_ = v___x_782_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_r_772_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v_r_760_);
v___x_832_ = v_reuseFailAlloc_845_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_isSharedCheck_839_ = !lean_is_exclusive(v_r_760_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_840_ = lean_ctor_get(v_r_760_, 4);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_r_760_, 3);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_r_760_, 2);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_r_760_, 1);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_r_760_, 0);
lean_dec(v_unused_844_);
v___x_834_ = v_r_760_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_r_760_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 4, v___x_832_);
lean_ctor_set(v___x_834_, 3, v_l_771_);
lean_ctor_set(v___x_834_, 2, v_v_770_);
lean_ctor_set(v___x_834_, 1, v_k_769_);
lean_ctor_set(v___x_834_, 0, v___x_828_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_838_, 3, v_l_771_);
lean_ctor_set(v_reuseFailAlloc_838_, 4, v___x_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_852_; 
v_l_852_ = lean_ctor_get(v_impl_765_, 3);
lean_inc(v_l_852_);
if (lean_obj_tag(v_l_852_) == 0)
{
lean_object* v_r_853_; lean_object* v_k_854_; lean_object* v_v_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_866_; 
v_r_853_ = lean_ctor_get(v_impl_765_, 4);
v_k_854_ = lean_ctor_get(v_impl_765_, 1);
v_v_855_ = lean_ctor_get(v_impl_765_, 2);
v_isSharedCheck_866_ = !lean_is_exclusive(v_impl_765_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; lean_object* v_unused_868_; 
v_unused_867_ = lean_ctor_get(v_impl_765_, 3);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_impl_765_, 0);
lean_dec(v_unused_868_);
v___x_857_ = v_impl_765_;
v_isShared_858_ = v_isSharedCheck_866_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_r_853_);
lean_inc(v_v_855_);
lean_inc(v_k_854_);
lean_dec(v_impl_765_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_866_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_853_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 3, v_r_853_);
lean_ctor_set(v___x_857_, 2, v_v_758_);
lean_ctor_set(v___x_857_, 1, v_k_757_);
lean_ctor_set(v___x_857_, 0, v___x_766_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_r_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_r_853_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v___x_861_);
lean_ctor_set(v___x_762_, 3, v_l_852_);
lean_ctor_set(v___x_762_, 2, v_v_855_);
lean_ctor_set(v___x_762_, 1, v_k_854_);
lean_ctor_set(v___x_762_, 0, v___x_859_);
v___x_863_ = v___x_762_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_k_854_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_v_855_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_l_852_);
lean_ctor_set(v_reuseFailAlloc_864_, 4, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_r_869_; 
v_r_869_ = lean_ctor_get(v_impl_765_, 4);
lean_inc(v_r_869_);
if (lean_obj_tag(v_r_869_) == 0)
{
lean_object* v_k_870_; lean_object* v_v_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_894_; 
v_k_870_ = lean_ctor_get(v_impl_765_, 1);
v_v_871_ = lean_ctor_get(v_impl_765_, 2);
v_isSharedCheck_894_ = !lean_is_exclusive(v_impl_765_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; lean_object* v_unused_896_; lean_object* v_unused_897_; 
v_unused_895_ = lean_ctor_get(v_impl_765_, 4);
lean_dec(v_unused_895_);
v_unused_896_ = lean_ctor_get(v_impl_765_, 3);
lean_dec(v_unused_896_);
v_unused_897_ = lean_ctor_get(v_impl_765_, 0);
lean_dec(v_unused_897_);
v___x_873_ = v_impl_765_;
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_v_871_);
lean_inc(v_k_870_);
lean_dec(v_impl_765_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_894_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_k_875_; lean_object* v_v_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_890_; 
v_k_875_ = lean_ctor_get(v_r_869_, 1);
v_v_876_ = lean_ctor_get(v_r_869_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_r_869_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_891_ = lean_ctor_get(v_r_869_, 4);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_r_869_, 3);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_r_869_, 0);
lean_dec(v_unused_893_);
v___x_878_ = v_r_869_;
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_v_876_);
lean_inc(v_k_875_);
lean_dec(v_r_869_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_unsigned_to_nat(3u);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 4, v_l_852_);
lean_ctor_set(v___x_878_, 3, v_l_852_);
lean_ctor_set(v___x_878_, 2, v_v_871_);
lean_ctor_set(v___x_878_, 1, v_k_870_);
lean_ctor_set(v___x_878_, 0, v___x_766_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_870_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_871_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_l_852_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_l_852_);
v___x_882_ = v_reuseFailAlloc_889_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 4, v_l_852_);
lean_ctor_set(v___x_873_, 2, v_v_758_);
lean_ctor_set(v___x_873_, 1, v_k_757_);
lean_ctor_set(v___x_873_, 0, v___x_766_);
v___x_884_ = v___x_873_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_l_852_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_l_852_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v___x_884_);
lean_ctor_set(v___x_762_, 3, v___x_882_);
lean_ctor_set(v___x_762_, 2, v_v_876_);
lean_ctor_set(v___x_762_, 1, v_k_875_);
lean_ctor_set(v___x_762_, 0, v___x_880_);
v___x_886_ = v___x_762_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_k_875_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_v_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 3, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_887_, 4, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
else
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_unsigned_to_nat(2u);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v_r_869_);
lean_ctor_set(v___x_762_, 3, v_impl_765_);
lean_ctor_set(v___x_762_, 0, v___x_898_);
v___x_900_ = v___x_762_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v_impl_765_);
lean_ctor_set(v_reuseFailAlloc_901_, 4, v_r_869_);
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
}
case 1:
{
lean_object* v___x_903_; 
lean_dec(v_v_758_);
lean_dec(v_k_757_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 2, v_v_754_);
lean_ctor_set(v___x_762_, 1, v_k_753_);
v___x_903_ = v___x_762_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_size_756_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_k_753_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_v_754_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_l_759_);
lean_ctor_set(v_reuseFailAlloc_904_, 4, v_r_760_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
default: 
{
lean_object* v_impl_905_; lean_object* v___x_906_; 
lean_dec(v_size_756_);
v_impl_905_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_753_, v_v_754_, v_r_760_);
v___x_906_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_759_) == 0)
{
lean_object* v_size_907_; lean_object* v_size_908_; lean_object* v_k_909_; lean_object* v_v_910_; lean_object* v_l_911_; lean_object* v_r_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_size_907_ = lean_ctor_get(v_l_759_, 0);
v_size_908_ = lean_ctor_get(v_impl_905_, 0);
lean_inc(v_size_908_);
v_k_909_ = lean_ctor_get(v_impl_905_, 1);
lean_inc(v_k_909_);
v_v_910_ = lean_ctor_get(v_impl_905_, 2);
lean_inc(v_v_910_);
v_l_911_ = lean_ctor_get(v_impl_905_, 3);
lean_inc(v_l_911_);
v_r_912_ = lean_ctor_get(v_impl_905_, 4);
lean_inc(v_r_912_);
v___x_913_ = lean_unsigned_to_nat(3u);
v___x_914_ = lean_nat_mul(v___x_913_, v_size_907_);
v___x_915_ = lean_nat_dec_lt(v___x_914_, v_size_908_);
lean_dec(v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
lean_dec(v_r_912_);
lean_dec(v_l_911_);
lean_dec(v_v_910_);
lean_dec(v_k_909_);
v___x_916_ = lean_nat_add(v___x_906_, v_size_907_);
v___x_917_ = lean_nat_add(v___x_916_, v_size_908_);
lean_dec(v_size_908_);
lean_dec(v___x_916_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v_impl_905_);
lean_ctor_set(v___x_762_, 0, v___x_917_);
v___x_919_ = v___x_762_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_l_759_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_impl_905_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
else
{
lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_984_; 
v_isSharedCheck_984_ = !lean_is_exclusive(v_impl_905_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_985_ = lean_ctor_get(v_impl_905_, 4);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_impl_905_, 3);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_impl_905_, 2);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_impl_905_, 1);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_impl_905_, 0);
lean_dec(v_unused_989_);
v___x_922_ = v_impl_905_;
v_isShared_923_ = v_isSharedCheck_984_;
goto v_resetjp_921_;
}
else
{
lean_dec(v_impl_905_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_984_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_size_924_; lean_object* v_k_925_; lean_object* v_v_926_; lean_object* v_l_927_; lean_object* v_r_928_; lean_object* v_size_929_; lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_size_924_ = lean_ctor_get(v_l_911_, 0);
v_k_925_ = lean_ctor_get(v_l_911_, 1);
v_v_926_ = lean_ctor_get(v_l_911_, 2);
v_l_927_ = lean_ctor_get(v_l_911_, 3);
v_r_928_ = lean_ctor_get(v_l_911_, 4);
v_size_929_ = lean_ctor_get(v_r_912_, 0);
v___x_930_ = lean_unsigned_to_nat(2u);
v___x_931_ = lean_nat_mul(v___x_930_, v_size_929_);
v___x_932_ = lean_nat_dec_lt(v_size_924_, v___x_931_);
lean_dec(v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_960_; 
lean_inc(v_r_928_);
lean_inc(v_l_927_);
lean_inc(v_v_926_);
lean_inc(v_k_925_);
v_isSharedCheck_960_ = !lean_is_exclusive(v_l_911_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; 
v_unused_961_ = lean_ctor_get(v_l_911_, 4);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_l_911_, 3);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_911_, 2);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_l_911_, 1);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_l_911_, 0);
lean_dec(v_unused_965_);
v___x_934_ = v_l_911_;
v_isShared_935_ = v_isSharedCheck_960_;
goto v_resetjp_933_;
}
else
{
lean_dec(v_l_911_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_960_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_950_; 
v___x_936_ = lean_nat_add(v___x_906_, v_size_907_);
v___x_937_ = lean_nat_add(v___x_936_, v_size_908_);
lean_dec(v_size_908_);
if (lean_obj_tag(v_l_927_) == 0)
{
lean_object* v_size_958_; 
v_size_958_ = lean_ctor_get(v_l_927_, 0);
lean_inc(v_size_958_);
v___y_950_ = v_size_958_;
goto v___jp_949_;
}
else
{
lean_object* v___x_959_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___y_950_ = v___x_959_;
goto v___jp_949_;
}
v___jp_938_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_nat_add(v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec(v___y_940_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 4, v_r_912_);
lean_ctor_set(v___x_934_, 3, v_r_928_);
lean_ctor_set(v___x_934_, 2, v_v_910_);
lean_ctor_set(v___x_934_, 1, v_k_909_);
lean_ctor_set(v___x_934_, 0, v___x_942_);
v___x_944_ = v___x_934_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_k_909_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_v_910_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_r_928_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_r_912_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 4, v___x_944_);
lean_ctor_set(v___x_922_, 3, v___y_939_);
lean_ctor_set(v___x_922_, 2, v_v_926_);
lean_ctor_set(v___x_922_, 1, v_k_925_);
lean_ctor_set(v___x_922_, 0, v___x_937_);
v___x_946_ = v___x_922_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_k_925_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_v_926_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v___y_939_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_nat_add(v___x_936_, v___y_950_);
lean_dec(v___y_950_);
lean_dec(v___x_936_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v_l_927_);
lean_ctor_set(v___x_762_, 0, v___x_951_);
v___x_953_ = v___x_762_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_l_759_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_l_927_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_nat_add(v___x_906_, v_size_929_);
if (lean_obj_tag(v_r_928_) == 0)
{
lean_object* v_size_955_; 
v_size_955_ = lean_ctor_get(v_r_928_, 0);
lean_inc(v_size_955_);
v___y_939_ = v___x_953_;
v___y_940_ = v___x_954_;
v___y_941_ = v_size_955_;
goto v___jp_938_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___y_939_ = v___x_953_;
v___y_940_ = v___x_954_;
v___y_941_ = v___x_956_;
goto v___jp_938_;
}
}
}
}
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
lean_del_object(v___x_762_);
v___x_966_ = lean_nat_add(v___x_906_, v_size_907_);
v___x_967_ = lean_nat_add(v___x_966_, v_size_908_);
lean_dec(v_size_908_);
v___x_968_ = lean_nat_add(v___x_966_, v_size_924_);
lean_dec(v___x_966_);
lean_inc_ref(v_l_759_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 4, v_l_911_);
lean_ctor_set(v___x_922_, 3, v_l_759_);
lean_ctor_set(v___x_922_, 2, v_v_758_);
lean_ctor_set(v___x_922_, 1, v_k_757_);
lean_ctor_set(v___x_922_, 0, v___x_968_);
v___x_970_ = v___x_922_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v_l_759_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v_l_911_);
v___x_970_ = v_reuseFailAlloc_983_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_isSharedCheck_977_ = !lean_is_exclusive(v_l_759_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; lean_object* v_unused_979_; lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; 
v_unused_978_ = lean_ctor_get(v_l_759_, 4);
lean_dec(v_unused_978_);
v_unused_979_ = lean_ctor_get(v_l_759_, 3);
lean_dec(v_unused_979_);
v_unused_980_ = lean_ctor_get(v_l_759_, 2);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_l_759_, 1);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_l_759_, 0);
lean_dec(v_unused_982_);
v___x_972_ = v_l_759_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_dec(v_l_759_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 4, v_r_912_);
lean_ctor_set(v___x_972_, 3, v___x_970_);
lean_ctor_set(v___x_972_, 2, v_v_910_);
lean_ctor_set(v___x_972_, 1, v_k_909_);
lean_ctor_set(v___x_972_, 0, v___x_967_);
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_909_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_910_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_r_912_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_990_; 
v_l_990_ = lean_ctor_get(v_impl_905_, 3);
lean_inc(v_l_990_);
if (lean_obj_tag(v_l_990_) == 0)
{
lean_object* v_r_991_; lean_object* v_k_992_; lean_object* v_v_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1016_; 
v_r_991_ = lean_ctor_get(v_impl_905_, 4);
v_k_992_ = lean_ctor_get(v_impl_905_, 1);
v_v_993_ = lean_ctor_get(v_impl_905_, 2);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_impl_905_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1017_ = lean_ctor_get(v_impl_905_, 3);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_impl_905_, 0);
lean_dec(v_unused_1018_);
v___x_995_ = v_impl_905_;
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_r_991_);
lean_inc(v_v_993_);
lean_inc(v_k_992_);
lean_dec(v_impl_905_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_k_997_; lean_object* v_v_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1012_; 
v_k_997_ = lean_ctor_get(v_l_990_, 1);
v_v_998_ = lean_ctor_get(v_l_990_, 2);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_l_990_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; lean_object* v_unused_1014_; lean_object* v_unused_1015_; 
v_unused_1013_ = lean_ctor_get(v_l_990_, 4);
lean_dec(v_unused_1013_);
v_unused_1014_ = lean_ctor_get(v_l_990_, 3);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_l_990_, 0);
lean_dec(v_unused_1015_);
v___x_1000_ = v_l_990_;
v_isShared_1001_ = v_isSharedCheck_1012_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_v_998_);
lean_inc(v_k_997_);
lean_dec(v_l_990_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1012_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_991_, 2);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 4, v_r_991_);
lean_ctor_set(v___x_1000_, 3, v_r_991_);
lean_ctor_set(v___x_1000_, 2, v_v_758_);
lean_ctor_set(v___x_1000_, 1, v_k_757_);
lean_ctor_set(v___x_1000_, 0, v___x_906_);
v___x_1004_ = v___x_1000_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_r_991_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_991_);
v___x_1004_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; 
lean_inc(v_r_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 3, v_r_991_);
lean_ctor_set(v___x_995_, 0, v___x_906_);
v___x_1006_ = v___x_995_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_992_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_993_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_r_991_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_r_991_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v___x_1006_);
lean_ctor_set(v___x_762_, 3, v___x_1004_);
lean_ctor_set(v___x_762_, 2, v_v_998_);
lean_ctor_set(v___x_762_, 1, v_k_997_);
lean_ctor_set(v___x_762_, 0, v___x_1002_);
v___x_1008_ = v___x_762_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
else
{
lean_object* v_r_1019_; 
v_r_1019_ = lean_ctor_get(v_impl_905_, 4);
lean_inc(v_r_1019_);
if (lean_obj_tag(v_r_1019_) == 0)
{
lean_object* v_k_1020_; lean_object* v_v_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1032_; 
v_k_1020_ = lean_ctor_get(v_impl_905_, 1);
v_v_1021_ = lean_ctor_get(v_impl_905_, 2);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_impl_905_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; lean_object* v_unused_1034_; lean_object* v_unused_1035_; 
v_unused_1033_ = lean_ctor_get(v_impl_905_, 4);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_impl_905_, 3);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_impl_905_, 0);
lean_dec(v_unused_1035_);
v___x_1023_ = v_impl_905_;
v_isShared_1024_ = v_isSharedCheck_1032_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_v_1021_);
lean_inc(v_k_1020_);
lean_dec(v_impl_905_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1032_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = lean_unsigned_to_nat(3u);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 4, v_l_990_);
lean_ctor_set(v___x_1023_, 2, v_v_758_);
lean_ctor_set(v___x_1023_, 1, v_k_757_);
lean_ctor_set(v___x_1023_, 0, v___x_906_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_l_990_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_l_990_);
v___x_1027_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v_r_1019_);
lean_ctor_set(v___x_762_, 3, v___x_1027_);
lean_ctor_set(v___x_762_, 2, v_v_1021_);
lean_ctor_set(v___x_762_, 1, v_k_1020_);
lean_ctor_set(v___x_762_, 0, v___x_1025_);
v___x_1029_ = v___x_762_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_1021_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_r_1019_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_unsigned_to_nat(2u);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 4, v_impl_905_);
lean_ctor_set(v___x_762_, 3, v_r_1019_);
lean_ctor_set(v___x_762_, 0, v___x_1036_);
v___x_1038_ = v___x_762_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_757_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_758_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_r_1019_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_impl_905_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
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
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_k_753_);
lean_ctor_set(v___x_1042_, 2, v_v_754_);
lean_ctor_set(v___x_1042_, 3, v_t_755_);
lean_ctor_set(v___x_1042_, 4, v_t_755_);
return v___x_1042_;
}
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = lean_box(1);
v___x_1044_ = l_Lake_ExternLib_defaultFacetConfig;
v___x_1045_ = l_Lake_ExternLib_defaultFacet;
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1045_, v___x_1044_, v___x_1043_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1047_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__0, &l_Lake_ExternLib_initFacetConfigs___closed__0_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__0);
v___x_1048_ = l_Lake_ExternLib_staticFacetConfig;
v___x_1049_ = l_Lake_ExternLib_staticFacet;
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1049_, v___x_1048_, v___x_1047_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__1, &l_Lake_ExternLib_initFacetConfigs___closed__1_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__1);
v___x_1052_ = l_Lake_ExternLib_sharedFacetConfig;
v___x_1053_ = l_Lake_ExternLib_sharedFacet;
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1053_, v___x_1052_, v___x_1051_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__2, &l_Lake_ExternLib_initFacetConfigs___closed__2_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__2);
v___x_1056_ = l_Lake_ExternLib_dynlibFacetConfig;
v___x_1057_ = l_Lake_ExternLib_dynlibFacet;
v___x_1058_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v___x_1057_, v___x_1056_, v___x_1055_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_obj_once(&l_Lake_ExternLib_initFacetConfigs___closed__3, &l_Lake_ExternLib_initFacetConfigs___closed__3_once, _init_l_Lake_ExternLib_initFacetConfigs___closed__3);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_1060_, lean_object* v_k_1061_, lean_object* v_v_1062_, lean_object* v_t_1063_, lean_object* v_hl_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_ExternLib_initFacetConfigs_spec__0___redArg(v_k_1061_, v_v_1062_, v_t_1063_);
return v___x_1065_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_ExternLib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
