// Lean compiler output
// Module: Lake.Build.Executable
// Imports: public import Lake.Config.FacetConfig import Lake.Build.Job.Register import Lake.Build.Target.Fetch import Lake.Build.Common import Lake.Build.Infos
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
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "type mismatch in target '"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0_value;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "': expected '"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1_value;
extern lean_object* l_Lake_instDataKindDynlib;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_once_cell_t l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "', got "};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3_value;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4_value;
static const lean_string_object l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5 = (const lean_object*)&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5_value;
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
static lean_once_cell_t l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0;
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2 = (const lean_object*)&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2_value;
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13;
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ModuleFacet_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0_value;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
static lean_once_cell_t l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1;
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "bad imports (see the '"};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "' job for details)"};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3_value;
extern lean_object* l_Lake_Module_transImportsFacet;
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_io_wait(lean_object*);
extern lean_object* l_Lake_Package_transDepsFacet;
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_LeanExe_linkArgs(lean_object*);
extern uint8_t l_System_Platform_isWindows;
uint8_t lean_strict_and(uint8_t, uint8_t);
lean_object* l_Lake_buildLeanExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(lean_object**);
static const lean_array_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0_value;
static const lean_string_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ":exe"};
static const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1 = (const lean_object*)&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1_value;
lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanExe_exeFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanExe_exeFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanExe_exeFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_LeanExe_exeFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanExe_exeFacetConfig___closed__1 = (const lean_object*)&l_Lake_LeanExe_exeFacetConfig___closed__1_value;
extern lean_object* l_Lake_LeanExe_keyword;
static lean_once_cell_t l_Lake_LeanExe_exeFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_exeFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeFacetConfig;
extern lean_object* l_Lake_LeanExe_exeFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanExe_defaultFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanExe_defaultFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanExe_defaultFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_LeanExe_defaultFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_defaultFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanExe_defaultFacetConfig;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_defaultFacet;
static lean_once_cell_t l_Lake_LeanExe_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_initFacetConfigs___closed__0;
static lean_once_cell_t l_Lake_LeanExe_initFacetConfigs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanExe_initFacetConfigs___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanExe_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_instDataKindDynlib;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc_ref_n(x_2, 2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_54; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_12, 0);
lean_dec(x_55);
x_14 = x_12;
x_15 = x_54;
goto block_53;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_51; 
x_16 = lean_ctor_get(x_11, 1);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_11, 0);
lean_dec(x_52);
x_17 = x_11;
x_18 = x_51;
goto block_50;
}
else
{
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_40; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = l_Lake_instDataKindDynlib;
x_40 = lean_name_eq(x_19, x_20);
if (x_40 == 0)
{
uint8_t x_41; 
lean_inc(x_19);
lean_del_object(x_14);
lean_dec(x_13);
x_41 = l_Lean_Name_isAnonymous(x_19);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4));
x_43 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_19, x_10);
x_44 = lean_string_append(x_42, x_43);
lean_dec_ref(x_43);
x_45 = lean_string_append(x_44, x_42);
x_21 = x_45;
goto block_39;
}
else
{
lean_object* x_46; 
lean_dec(x_19);
x_46 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5));
x_21 = x_46;
goto block_39;
}
}
else
{
lean_object* x_47; 
lean_del_object(x_17);
lean_dec_ref(x_2);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_13);
x_47 = x_14;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_16);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
block_39:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0));
x_23 = l_Lake_PartialBuildKey_toString(x_2);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1));
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__2);
x_28 = lean_string_append(x_26, x_27);
x_29 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_21);
lean_dec_ref(x_21);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_16);
x_35 = lean_array_push(x_16, x_33);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_34);
x_36 = x_17;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
x_64 = !lean_is_exclusive(x_11);
if (x_64 == 0)
{
x_58 = x_11;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_instDataKindFilePath;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc_ref_n(x_2, 2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_54; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_12, 0);
lean_dec(x_55);
x_14 = x_12;
x_15 = x_54;
goto block_53;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_51; 
x_16 = lean_ctor_get(x_11, 1);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_11, 0);
lean_dec(x_52);
x_17 = x_11;
x_18 = x_51;
goto block_50;
}
else
{
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_40; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = l_Lake_instDataKindFilePath;
x_40 = lean_name_eq(x_19, x_20);
if (x_40 == 0)
{
uint8_t x_41; 
lean_inc(x_19);
lean_del_object(x_14);
lean_dec(x_13);
x_41 = l_Lean_Name_isAnonymous(x_19);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__4));
x_43 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_19, x_10);
x_44 = lean_string_append(x_42, x_43);
lean_dec_ref(x_43);
x_45 = lean_string_append(x_44, x_42);
x_21 = x_45;
goto block_39;
}
else
{
lean_object* x_46; 
lean_dec(x_19);
x_46 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__5));
x_21 = x_46;
goto block_39;
}
}
else
{
lean_object* x_47; 
lean_del_object(x_17);
lean_dec_ref(x_2);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_13);
x_47 = x_14;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_16);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
block_39:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__0));
x_23 = l_Lake_PartialBuildKey_toString(x_2);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__1));
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___closed__0);
x_28 = lean_string_append(x_26, x_27);
x_29 = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3___closed__3));
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_21);
lean_dec_ref(x_21);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_16);
x_35 = lean_array_push(x_16, x_33);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_34);
x_36 = x_17;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
x_64 = !lean_is_exclusive(x_11);
if (x_64 == 0)
{
x_58 = x_11;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__2));
x_2 = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13___closed__3);
return x_1;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_32; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
x_6 = x_2;
x_7 = x_32;
goto block_31;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_array_get_size(x_1);
if (lean_obj_tag(x_8) == 0)
{
uint64_t x_29; 
x_29 = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
x_10 = x_29;
goto block_28;
}
else
{
uint64_t x_30; 
x_30 = lean_ctor_get_uint64(x_8, sizeof(void*)*2);
x_10 = x_30;
goto block_28;
}
block_28:
{
uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_9);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget_borrowed(x_1, x_21);
lean_inc(x_22);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_22);
x_23 = x_6;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_22);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; 
x_24 = lean_array_uset(x_1, x_21, x_23);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_array_get_size(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint64_t x_46; 
x_46 = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
x_8 = x_46;
goto block_45;
}
else
{
uint64_t x_47; 
x_47 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
x_8 = x_47;
goto block_45;
}
block_45:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_5, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_42; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 0);
lean_dec(x_44);
x_22 = x_1;
x_23 = x_42;
goto block_41;
}
else
{
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
lean_inc(x_20);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_20);
x_27 = lean_array_uset(x_5, x_19, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(x_27);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_34);
lean_ctor_set(x_22, 0, x_25);
x_35 = x_22;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
else
{
lean_object* x_38; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_27);
lean_ctor_set(x_22, 0, x_25);
x_38 = x_22;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_27);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint64_t x_21; 
x_21 = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg___closed__0);
x_6 = x_21;
goto block_20;
}
else
{
uint64_t x_22; 
x_22 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_6 = x_22;
goto block_20;
}
block_20:
{
uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget_borrowed(x_3, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(x_2, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_15; 
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_6 = x_1;
x_7 = x_15;
goto block_14;
}
else
{
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
lean_inc_ref(x_2);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(x_3, x_2, x_8);
x_10 = lean_array_push(x_4, x_2);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_10);
lean_ctor_set(x_6, 0, x_9);
x_11 = x_6;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget_borrowed(x_2, x_4);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_15);
lean_inc_ref(x_1);
x_16 = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_array_push(x_5, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
x_25 = x_16;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_array_uget_borrowed(x_2, x_4);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_16);
lean_inc_ref(x_15);
x_17 = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__3(x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_array_push(x_5, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_5 = x_20;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_26 = x_17;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_array_uget_borrowed(x_2, x_4);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_16);
lean_inc_ref(x_15);
x_17 = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_array_push(x_5, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_5 = x_20;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_26 = x_17;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_54; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_54 = !lean_is_exclusive(x_4);
if (x_54 == 0)
{
x_20 = x_4;
x_21 = x_54;
goto block_53;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_22 = lean_array_uget_borrowed(x_1, x_3);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_23, 6);
x_25 = lean_ctor_get(x_24, 1);
x_26 = lean_ctor_get(x_22, 2);
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_ctor_get(x_25, 6);
x_29 = lean_ctor_get(x_25, 7);
x_30 = lean_ctor_get(x_27, 6);
x_31 = lean_ctor_get(x_27, 7);
lean_inc_ref(x_28);
x_32 = l_Array_append___redArg(x_28, x_30);
x_33 = lean_array_size(x_32);
x_34 = 0;
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_22);
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__5(x_22, x_32, x_33, x_34, x_19, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
lean_inc_ref(x_29);
x_38 = l_Array_append___redArg(x_29, x_31);
x_39 = lean_array_size(x_38);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_22);
x_40 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__6(x_22, x_38, x_39, x_34, x_18, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec_ref(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_36);
lean_ctor_set(x_20, 0, x_41);
x_43 = x_20;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_36);
x_43 = x_48;
goto block_47;
}
block_47:
{
size_t x_44; size_t x_45; 
x_44 = 1;
x_45 = lean_usize_add(x_3, x_44);
x_3 = x_45;
x_4 = x_43;
x_10 = x_42;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_36);
lean_del_object(x_20);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec_ref(x_40);
x_12 = x_49;
x_13 = x_50;
goto block_15;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_del_object(x_20);
lean_dec(x_18);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_51 = lean_ctor_get(x_35, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_dec_ref(x_35);
x_12 = x_51;
x_13 = x_52;
goto block_15;
}
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget_borrowed(x_2, x_4);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_15);
lean_inc_ref(x_1);
x_16 = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__4(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_array_push(x_5, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
x_25 = x_16;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget_borrowed(x_2, x_4);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
lean_inc(x_15);
x_16 = l_Lake_ModuleFacet_fetch___redArg(x_15, x_1, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_array_push(x_5, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
x_5 = x_19;
x_11 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
x_25 = x_16;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_15 = lean_array_uget_borrowed(x_2, x_4);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_16, 2);
x_18 = lean_ctor_get(x_17, 8);
x_19 = lean_box(x_1);
lean_inc_ref(x_18);
x_20 = lean_apply_1(x_18, x_19);
x_21 = lean_array_size(x_20);
x_22 = 0;
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_15);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(x_15, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_24;
x_11 = x_25;
goto _start;
}
else
{
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_array_uget_borrowed(x_2, x_3);
x_13 = lean_ctor_get(x_12, 1);
x_14 = lean_ctor_get(x_12, 2);
x_15 = lean_ctor_get(x_12, 3);
x_16 = l_Lake_ExternLib_keyword;
x_17 = lean_name_eq(x_14, x_16);
if (x_17 == 0)
{
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_15);
lean_inc(x_13);
lean_inc_ref(x_1);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_15);
x_19 = lean_array_push(x_5, x_18);
x_6 = x_19;
goto block_10;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_array_uget_borrowed(x_1, x_3);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_15, 2);
x_18 = l_Lake_ExternLib_staticFacet;
lean_inc(x_16);
lean_inc(x_17);
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
x_20 = l_Lake_ExternLib_keyword;
lean_inc(x_14);
x_21 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_18);
lean_inc_ref(x_5);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = lean_apply_7(x_5, x_21, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_array_push(x_4, x_23);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_4 = x_25;
x_10 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
x_31 = x_22;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_3, x_2);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_array_uget_borrowed(x_1, x_3);
x_25 = lean_ctor_get(x_24, 13);
x_26 = lean_unsigned_to_nat(0u);
x_27 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___closed__0));
x_28 = lean_array_get_size(x_25);
x_29 = lean_nat_dec_lt(x_26, x_28);
if (x_29 == 0)
{
x_12 = x_27;
goto block_21;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
if (x_29 == 0)
{
x_12 = x_27;
goto block_21;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_28);
lean_inc(x_24);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(x_24, x_25, x_31, x_32, x_27);
x_12 = x_33;
goto block_21;
}
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_28);
lean_inc(x_24);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__2(x_24, x_25, x_34, x_35, x_27);
x_12 = x_36;
goto block_21;
}
}
}
block_21:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_array_size(x_12);
x_14 = 0;
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__1(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_16;
x_10 = x_17;
goto _start;
}
else
{
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__0));
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; 
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_1);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__7(x_1, x_2, x_3, x_4, x_5, x_15, x_6, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_7, 6);
lean_inc_ref(x_27);
x_28 = l_Lake_Module_transImportsFacet;
lean_inc(x_8);
lean_inc(x_25);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_8);
x_30 = l_Lake_Module_keyword;
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_1);
lean_ctor_set(x_31, 3, x_28);
lean_inc_ref(x_15);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
x_32 = lean_apply_7(x_15, x_31, x_6, x_17, x_18, x_19, x_24, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_196; 
x_33 = lean_ctor_get(x_32, 0);
x_34 = lean_ctor_get(x_32, 1);
x_196 = !lean_is_exclusive(x_32);
if (x_196 == 0)
{
x_35 = x_32;
x_36 = x_196;
goto block_195;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_37);
lean_dec(x_33);
x_38 = lean_io_wait(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; size_t x_40; lean_object* x_41; 
lean_del_object(x_35);
lean_dec(x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_array_size(x_39);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
lean_inc_ref(x_15);
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__8(x_9, x_39, x_40, x_4, x_23, x_15, x_6, x_17, x_18, x_19, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_ctor_get(x_10, 6);
x_45 = lean_ctor_get(x_10, 7);
x_46 = lean_ctor_get(x_10, 9);
x_47 = lean_array_size(x_44);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_7);
x_48 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__9(x_7, x_44, x_47, x_4, x_42, x_15, x_6, x_17, x_18, x_19, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_156 = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13;
x_157 = lean_array_get_size(x_39);
x_158 = lean_nat_dec_lt(x_14, x_157);
if (x_158 == 0)
{
lean_dec(x_39);
x_51 = x_156;
goto block_155;
}
else
{
uint8_t x_159; 
x_159 = lean_nat_dec_le(x_157, x_157);
if (x_159 == 0)
{
if (x_158 == 0)
{
lean_dec(x_39);
x_51 = x_156;
goto block_155;
}
else
{
size_t x_160; lean_object* x_161; 
x_160 = lean_usize_of_nat(x_157);
x_161 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(x_39, x_4, x_160, x_156);
lean_dec(x_39);
x_51 = x_161;
goto block_155;
}
}
else
{
size_t x_162; lean_object* x_163; 
x_162 = lean_usize_of_nat(x_157);
x_163 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__14(x_39, x_4, x_162, x_156);
lean_dec(x_39);
x_51 = x_163;
goto block_155;
}
}
block_155:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_153; 
x_52 = lean_ctor_get(x_51, 1);
x_153 = !lean_is_exclusive(x_51);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_51, 0);
lean_dec(x_154);
x_53 = x_51;
x_54 = x_153;
goto block_152;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_55; 
if (x_54 == 0)
{
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 0, x_11);
x_55 = x_53;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_11);
lean_ctor_set(x_151, 1, x_49);
x_55 = x_151;
goto block_150;
}
block_150:
{
size_t x_56; lean_object* x_57; 
x_56 = lean_array_size(x_52);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
lean_inc_ref(x_15);
x_57 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__10(x_52, x_56, x_4, x_55, x_15, x_6, x_17, x_18, x_19, x_50);
lean_dec_ref(x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_array_size(x_45);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_7);
x_63 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__11(x_7, x_45, x_62, x_4, x_60, x_15, x_6, x_17, x_18, x_19, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Lake_Package_transDepsFacet;
lean_inc(x_25);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_25);
x_68 = l_Lake_Package_keyword;
lean_inc_ref(x_7);
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_7);
lean_ctor_set(x_69, 3, x_66);
lean_inc_ref(x_15);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
x_70 = lean_apply_7(x_15, x_69, x_6, x_17, x_18, x_19, x_65, lean_box(0));
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = l_Lake_Job_await___redArg(x_71, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_array_push(x_74, x_7);
x_77 = lean_array_size(x_76);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_6);
lean_inc_ref(x_15);
x_78 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__12(x_76, x_77, x_4, x_61, x_15, x_6, x_17, x_18, x_19, x_75);
lean_dec_ref(x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_104; 
x_79 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
x_104 = !lean_is_exclusive(x_78);
if (x_104 == 0)
{
x_82 = x_78;
x_83 = x_104;
goto block_103;
}
else
{
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_box(0);
x_83 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_84 = lean_ctor_get(x_27, 6);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_27, 9);
lean_inc_ref(x_85);
lean_dec_ref(x_27);
x_86 = lean_ctor_get(x_79, 9);
lean_inc_ref(x_86);
lean_dec_ref(x_79);
x_87 = l_System_FilePath_normalize(x_84);
x_88 = l_Lake_joinRelative(x_26, x_87);
x_89 = l_System_FilePath_normalize(x_85);
x_90 = l_Lake_joinRelative(x_88, x_89);
x_91 = l_System_FilePath_exeExtension;
x_92 = l_System_FilePath_addExtension(x_12, x_91);
x_93 = l_Lake_joinRelative(x_90, x_92);
x_94 = l_Array_append___redArg(x_86, x_46);
x_95 = l_Lake_LeanExe_linkArgs(x_13);
x_96 = l_System_Platform_isWindows;
x_97 = lean_strict_and(x_96, x_9);
x_98 = lean_obj_once(&l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1, &l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1_once, _init_l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__1);
x_99 = l_Lake_buildLeanExe(x_93, x_80, x_64, x_94, x_95, x_97, x_15, x_6, x_17, x_18, x_19, x_98);
lean_dec(x_80);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_99);
x_100 = x_82;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_81);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_113; 
lean_dec(x_64);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_6);
x_105 = lean_ctor_get(x_78, 0);
x_106 = lean_ctor_get(x_78, 1);
x_113 = !lean_is_exclusive(x_78);
if (x_113 == 0)
{
x_107 = x_78;
x_108 = x_113;
goto block_112;
}
else
{
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_78);
x_107 = lean_box(0);
x_108 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_109; 
if (x_108 == 0)
{
x_109 = x_107;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_106);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_122; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
lean_dec(x_6);
x_114 = lean_ctor_get(x_73, 0);
x_115 = lean_ctor_get(x_73, 1);
x_122 = !lean_is_exclusive(x_73);
if (x_122 == 0)
{
x_116 = x_73;
x_117 = x_122;
goto block_121;
}
else
{
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_73);
x_116 = lean_box(0);
x_117 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_118; 
if (x_117 == 0)
{
x_118 = x_116;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
lean_dec(x_6);
x_123 = lean_ctor_get(x_70, 0);
x_124 = lean_ctor_get(x_70, 1);
x_131 = !lean_is_exclusive(x_70);
if (x_131 == 0)
{
x_125 = x_70;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_70);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_124);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_140; 
lean_dec(x_61);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
lean_dec(x_6);
x_132 = lean_ctor_get(x_63, 0);
x_133 = lean_ctor_get(x_63, 1);
x_140 = !lean_is_exclusive(x_63);
if (x_140 == 0)
{
x_134 = x_63;
x_135 = x_140;
goto block_139;
}
else
{
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_63);
x_134 = lean_box(0);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_135 == 0)
{
x_136 = x_134;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_133);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_149; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_7);
lean_dec(x_6);
x_141 = lean_ctor_get(x_57, 0);
x_142 = lean_ctor_get(x_57, 1);
x_149 = !lean_is_exclusive(x_57);
if (x_149 == 0)
{
x_143 = x_57;
x_144 = x_149;
goto block_148;
}
else
{
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_57);
x_143 = lean_box(0);
x_144 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_145; 
if (x_144 == 0)
{
x_145 = x_143;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_142);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec(x_39);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_6);
x_164 = lean_ctor_get(x_48, 0);
x_165 = lean_ctor_get(x_48, 1);
x_172 = !lean_is_exclusive(x_48);
if (x_172 == 0)
{
x_166 = x_48;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_48);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_164);
lean_ctor_set(x_170, 1, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_181; 
lean_dec(x_39);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_6);
x_173 = lean_ctor_get(x_41, 0);
x_174 = lean_ctor_get(x_41, 1);
x_181 = !lean_is_exclusive(x_41);
if (x_181 == 0)
{
x_175 = x_41;
x_176 = x_181;
goto block_180;
}
else
{
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_41);
x_175 = lean_box(0);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_176 == 0)
{
x_177 = x_175;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_179, 1, x_174);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
else
{
lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_38);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_23);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_6);
x_182 = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__2));
x_183 = 1;
x_184 = l_Lean_Name_toString(x_8, x_183);
x_185 = lean_string_append(x_182, x_184);
lean_dec_ref(x_184);
x_186 = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___closed__3));
x_187 = lean_string_append(x_185, x_186);
x_188 = 3;
x_189 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*1, x_188);
x_190 = lean_array_get_size(x_34);
x_191 = lean_array_push(x_34, x_189);
if (x_36 == 0)
{
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_191);
lean_ctor_set(x_35, 0, x_190);
x_192 = x_35;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_191);
x_192 = x_194;
goto block_193;
}
block_193:
{
return x_192;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_205; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_23);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_197 = lean_ctor_get(x_32, 0);
x_198 = lean_ctor_get(x_32, 1);
x_205 = !lean_is_exclusive(x_32);
if (x_205 == 0)
{
x_199 = x_32;
x_200 = x_205;
goto block_204;
}
else
{
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_32);
x_199 = lean_box(0);
x_200 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_201; 
if (x_200 == 0)
{
x_201 = x_199;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_197);
lean_ctor_set(x_203, 1, x_198);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_214; 
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_206 = lean_ctor_get(x_22, 0);
x_207 = lean_ctor_get(x_22, 1);
x_214 = !lean_is_exclusive(x_22);
if (x_214 == 0)
{
x_208 = x_22;
x_209 = x_214;
goto block_213;
}
else
{
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_22);
x_208 = lean_box(0);
x_209 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_210; 
if (x_209 == 0)
{
x_210 = x_208;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_206);
lean_ctor_set(x_212, 1, x_207);
x_210 = x_212;
goto block_211;
}
block_211:
{
return x_210;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
size_t x_22; size_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_23 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_24 = lean_unbox(x_9);
x_25 = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0(x_1, x_2, x_22, x_23, x_5, x_6, x_7, x_8, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_16);
lean_dec(x_14);
lean_dec_ref(x_10);
lean_dec_ref(x_2);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_16 = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(x_9);
x_17 = lean_ctor_get(x_16, 8);
lean_inc_ref(x_17);
x_18 = l_Lake_instDataKindFilePath;
x_19 = lean_unsigned_to_nat(0u);
x_20 = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__0));
lean_inc(x_11);
lean_inc_ref(x_10);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_16);
lean_inc(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
x_23 = lean_box(x_15);
x_24 = lean_apply_1(x_17, x_23);
x_25 = lean_array_size(x_24);
lean_inc_ref(x_10);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_10);
x_27 = lean_box_usize(x_25);
x_28 = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed__const__1));
x_29 = lean_box(x_15);
x_30 = lean_alloc_closure((void*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___lam__0___boxed), 21, 14);
lean_closure_set(x_30, 0, x_22);
lean_closure_set(x_30, 1, x_24);
lean_closure_set(x_30, 2, x_27);
lean_closure_set(x_30, 3, x_28);
lean_closure_set(x_30, 4, x_20);
lean_closure_set(x_30, 5, x_26);
lean_closure_set(x_30, 6, x_10);
lean_closure_set(x_30, 7, x_13);
lean_closure_set(x_30, 8, x_29);
lean_closure_set(x_30, 9, x_12);
lean_closure_set(x_30, 10, x_20);
lean_closure_set(x_30, 11, x_14);
lean_closure_set(x_30, 12, x_1);
lean_closure_set(x_30, 13, x_19);
lean_inc_ref(x_6);
x_31 = l_Lake_ensureJob___redArg(x_18, x_30, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_61; 
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
x_34 = x_31;
x_35 = x_61;
goto block_60;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_58; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
x_58 = !lean_is_exclusive(x_32);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_32, 2);
lean_dec(x_59);
x_38 = x_32;
x_39 = x_58;
goto block_57;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_6, 3);
lean_inc(x_40);
lean_dec_ref(x_6);
x_41 = lean_st_ref_take(x_40);
x_42 = 1;
x_43 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_11, x_42);
x_44 = ((lean_object*)(l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___closed__1));
x_45 = lean_string_append(x_43, x_44);
x_46 = 0;
if (x_39 == 0)
{
lean_ctor_set(x_38, 2, x_45);
x_47 = x_38;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_45);
x_47 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_46);
lean_inc_ref(x_47);
x_48 = l_Lake_Job_toOpaque___redArg(x_47);
x_49 = lean_array_push(x_41, x_48);
x_50 = lean_st_ref_set(x_40, x_49);
lean_dec(x_40);
x_51 = l_Lake_Job_renew___redArg(x_47);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_51);
x_52 = x_34;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_33);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_6);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__0_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__0_spec__1_spec__6_spec__18_spec__19___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkRelPathString(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Json_compress(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_formatQuery___at___00Lake_LeanExe_exeFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig___closed__2(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
x_2 = 1;
x_3 = l_Lake_instDataKindFilePath;
x_4 = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__1));
x_5 = l_Lake_LeanExe_keyword;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_2);
return x_6;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacetConfig(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_LeanExe_exeFacetConfig___closed__2, &l_Lake_LeanExe_exeFacetConfig___closed__2_once, _init_l_Lake_LeanExe_exeFacetConfig___closed__2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_9, 2);
x_12 = l_Lake_LeanExe_exeFacet;
lean_inc(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lake_LeanExe_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_12);
x_16 = lean_apply_7(x_2, x_15, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Build_Executable_0__Lake_LeanExe_recBuildDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig___closed__1(void) {
_start:
{
uint8_t x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = ((lean_object*)(l_Lake_LeanExe_exeFacetConfig___closed__0));
x_3 = 1;
x_4 = l_Lake_instDataKindFilePath;
x_5 = ((lean_object*)(l_Lake_LeanExe_defaultFacetConfig___closed__0));
x_6 = l_Lake_LeanExe_keyword;
x_7 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*4 + 1, x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacetConfig(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_LeanExe_defaultFacetConfig___closed__1, &l_Lake_LeanExe_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanExe_defaultFacetConfig___closed__1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_288; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_288 = !lean_is_exclusive(x_3);
if (x_288 == 0)
{
x_9 = x_3;
x_10 = x_288;
goto block_287;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_288;
goto block_287;
}
block_287:
{
uint8_t x_11; 
x_11 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_5);
switch (x_11) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(x_1, x_2, x_7);
x_13 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 4);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_23 = lean_nat_add(x_13, x_15);
lean_dec(x_15);
x_24 = lean_nat_add(x_23, x_14);
lean_dec(x_23);
if (x_10 == 0)
{
lean_ctor_set(x_9, 3, x_12);
lean_ctor_set(x_9, 0, x_24);
x_25 = x_9;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_6);
lean_ctor_set(x_27, 3, x_12);
lean_ctor_set(x_27, 4, x_8);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_93; 
x_93 = !lean_is_exclusive(x_12);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_12, 4);
lean_dec(x_94);
x_95 = lean_ctor_get(x_12, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_12, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_12, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_12, 0);
lean_dec(x_98);
x_28 = x_12;
x_29 = x_93;
goto block_92;
}
else
{
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
x_33 = lean_ctor_get(x_19, 2);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_mul(x_36, x_30);
x_38 = lean_nat_dec_lt(x_31, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_67; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_67 = !lean_is_exclusive(x_19);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_19, 4);
lean_dec(x_68);
x_69 = lean_ctor_get(x_19, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_19, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_19, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_19, 0);
lean_dec(x_72);
x_39 = x_19;
x_40 = x_67;
goto block_66;
}
else
{
lean_dec(x_19);
x_39 = lean_box(0);
x_40 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_54; lean_object* x_55; 
x_41 = lean_nat_add(x_13, x_15);
lean_dec(x_15);
x_42 = lean_nat_add(x_41, x_14);
lean_dec(x_41);
x_54 = lean_nat_add(x_13, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_34, 0);
lean_inc(x_64);
x_55 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = lean_unsigned_to_nat(0u);
x_55 = x_65;
goto block_63;
}
block_53:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_nat_add(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_8);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 2, x_6);
lean_ctor_set(x_39, 1, x_5);
lean_ctor_set(x_39, 0, x_46);
x_47 = x_39;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_5);
lean_ctor_set(x_52, 2, x_6);
lean_ctor_set(x_52, 3, x_35);
lean_ctor_set(x_52, 4, x_8);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_29 == 0)
{
lean_ctor_set(x_28, 4, x_47);
lean_ctor_set(x_28, 3, x_44);
lean_ctor_set(x_28, 2, x_33);
lean_ctor_set(x_28, 1, x_32);
lean_ctor_set(x_28, 0, x_42);
x_48 = x_28;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_32);
lean_ctor_set(x_50, 2, x_33);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
block_63:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_nat_add(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_34);
lean_ctor_set(x_9, 3, x_18);
lean_ctor_set(x_9, 2, x_17);
lean_ctor_set(x_9, 1, x_16);
lean_ctor_set(x_9, 0, x_56);
x_57 = x_9;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_16);
lean_ctor_set(x_62, 2, x_17);
lean_ctor_set(x_62, 3, x_18);
lean_ctor_set(x_62, 4, x_34);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
x_58 = lean_nat_add(x_13, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_35, 0);
lean_inc(x_59);
x_43 = x_58;
x_44 = x_57;
x_45 = x_59;
goto block_53;
}
else
{
lean_object* x_60; 
x_60 = lean_unsigned_to_nat(0u);
x_43 = x_58;
x_44 = x_57;
x_45 = x_60;
goto block_53;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_del_object(x_9);
x_73 = lean_nat_add(x_13, x_15);
lean_dec(x_15);
x_74 = lean_nat_add(x_73, x_14);
lean_dec(x_73);
x_75 = lean_nat_add(x_13, x_14);
x_76 = lean_nat_add(x_75, x_31);
lean_dec(x_75);
lean_inc_ref(x_8);
if (x_29 == 0)
{
lean_ctor_set(x_28, 4, x_8);
lean_ctor_set(x_28, 3, x_19);
lean_ctor_set(x_28, 2, x_6);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 0, x_76);
x_77 = x_28;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_91, 0, x_76);
lean_ctor_set(x_91, 1, x_5);
lean_ctor_set(x_91, 2, x_6);
lean_ctor_set(x_91, 3, x_19);
lean_ctor_set(x_91, 4, x_8);
x_77 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_78; uint8_t x_79; uint8_t x_84; 
x_84 = !lean_is_exclusive(x_8);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_8, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_8, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_8, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_8, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_8, 0);
lean_dec(x_89);
x_78 = x_8;
x_79 = x_84;
goto block_83;
}
else
{
lean_dec(x_8);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 3, x_18);
lean_ctor_set(x_78, 2, x_17);
lean_ctor_set(x_78, 1, x_16);
lean_ctor_set(x_78, 0, x_74);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_16);
lean_ctor_set(x_82, 2, x_17);
lean_ctor_set(x_82, 3, x_18);
lean_ctor_set(x_82, 4, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
}
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_12, 3);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_113; 
x_100 = lean_ctor_get(x_12, 4);
x_101 = lean_ctor_get(x_12, 1);
x_102 = lean_ctor_get(x_12, 2);
x_113 = !lean_is_exclusive(x_12);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_12, 3);
lean_dec(x_114);
x_115 = lean_ctor_get(x_12, 0);
lean_dec(x_115);
x_103 = x_12;
x_104 = x_113;
goto block_112;
}
else
{
lean_inc(x_100);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_12);
x_103 = lean_box(0);
x_104 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_unsigned_to_nat(3u);
lean_inc(x_100);
if (x_104 == 0)
{
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 2, x_6);
lean_ctor_set(x_103, 1, x_5);
lean_ctor_set(x_103, 0, x_13);
x_106 = x_103;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_13);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 3, x_100);
lean_ctor_set(x_111, 4, x_100);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_106);
lean_ctor_set(x_9, 3, x_99);
lean_ctor_set(x_9, 2, x_102);
lean_ctor_set(x_9, 1, x_101);
lean_ctor_set(x_9, 0, x_105);
x_107 = x_9;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_99);
lean_ctor_set(x_109, 4, x_106);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_12, 4);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_141; 
x_117 = lean_ctor_get(x_12, 1);
x_118 = lean_ctor_get(x_12, 2);
x_141 = !lean_is_exclusive(x_12);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_12, 4);
lean_dec(x_142);
x_143 = lean_ctor_get(x_12, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_12, 0);
lean_dec(x_144);
x_119 = x_12;
x_120 = x_141;
goto block_140;
}
else
{
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_12);
x_119 = lean_box(0);
x_120 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_136; 
x_121 = lean_ctor_get(x_116, 1);
x_122 = lean_ctor_get(x_116, 2);
x_136 = !lean_is_exclusive(x_116);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_116, 4);
lean_dec(x_137);
x_138 = lean_ctor_get(x_116, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_116, 0);
lean_dec(x_139);
x_123 = x_116;
x_124 = x_136;
goto block_135;
}
else
{
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_116);
x_123 = lean_box(0);
x_124 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_unsigned_to_nat(3u);
if (x_124 == 0)
{
lean_ctor_set(x_123, 4, x_99);
lean_ctor_set(x_123, 3, x_99);
lean_ctor_set(x_123, 2, x_118);
lean_ctor_set(x_123, 1, x_117);
lean_ctor_set(x_123, 0, x_13);
x_126 = x_123;
goto block_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_13);
lean_ctor_set(x_134, 1, x_117);
lean_ctor_set(x_134, 2, x_118);
lean_ctor_set(x_134, 3, x_99);
lean_ctor_set(x_134, 4, x_99);
x_126 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_127; 
if (x_120 == 0)
{
lean_ctor_set(x_119, 4, x_99);
lean_ctor_set(x_119, 2, x_6);
lean_ctor_set(x_119, 1, x_5);
lean_ctor_set(x_119, 0, x_13);
x_127 = x_119;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_13);
lean_ctor_set(x_132, 1, x_5);
lean_ctor_set(x_132, 2, x_6);
lean_ctor_set(x_132, 3, x_99);
lean_ctor_set(x_132, 4, x_99);
x_127 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_128; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_127);
lean_ctor_set(x_9, 3, x_126);
lean_ctor_set(x_9, 2, x_122);
lean_ctor_set(x_9, 1, x_121);
lean_ctor_set(x_9, 0, x_125);
x_128 = x_9;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_121);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_126);
lean_ctor_set(x_130, 4, x_127);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_116);
lean_ctor_set(x_9, 3, x_12);
lean_ctor_set(x_9, 0, x_145);
x_146 = x_9;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_5);
lean_ctor_set(x_148, 2, x_6);
lean_ctor_set(x_148, 3, x_12);
lean_ctor_set(x_148, 4, x_116);
x_146 = x_148;
goto block_147;
}
block_147:
{
return x_146;
}
}
}
}
}
case 1:
{
lean_object* x_149; 
lean_dec(x_6);
lean_dec(x_5);
if (x_10 == 0)
{
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 1, x_1);
x_149 = x_9;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_4);
lean_ctor_set(x_151, 1, x_1);
lean_ctor_set(x_151, 2, x_2);
lean_ctor_set(x_151, 3, x_7);
lean_ctor_set(x_151, 4, x_8);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
default: 
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_4);
x_152 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(x_1, x_2, x_8);
x_153 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_7, 0);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_152, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_152, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_152, 4);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_mul(x_160, x_154);
x_162 = lean_nat_dec_lt(x_161, x_155);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_163 = lean_nat_add(x_153, x_154);
x_164 = lean_nat_add(x_163, x_155);
lean_dec(x_155);
lean_dec(x_163);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_152);
lean_ctor_set(x_9, 0, x_164);
x_165 = x_9;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_5);
lean_ctor_set(x_167, 2, x_6);
lean_ctor_set(x_167, 3, x_7);
lean_ctor_set(x_167, 4, x_152);
x_165 = x_167;
goto block_166;
}
block_166:
{
return x_165;
}
}
else
{
lean_object* x_168; uint8_t x_169; uint8_t x_231; 
x_231 = !lean_is_exclusive(x_152);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_152, 4);
lean_dec(x_232);
x_233 = lean_ctor_get(x_152, 3);
lean_dec(x_233);
x_234 = lean_ctor_get(x_152, 2);
lean_dec(x_234);
x_235 = lean_ctor_get(x_152, 1);
lean_dec(x_235);
x_236 = lean_ctor_get(x_152, 0);
lean_dec(x_236);
x_168 = x_152;
x_169 = x_231;
goto block_230;
}
else
{
lean_dec(x_152);
x_168 = lean_box(0);
x_169 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_170 = lean_ctor_get(x_158, 0);
x_171 = lean_ctor_get(x_158, 1);
x_172 = lean_ctor_get(x_158, 2);
x_173 = lean_ctor_get(x_158, 3);
x_174 = lean_ctor_get(x_158, 4);
x_175 = lean_ctor_get(x_159, 0);
x_176 = lean_unsigned_to_nat(2u);
x_177 = lean_nat_mul(x_176, x_175);
x_178 = lean_nat_dec_lt(x_170, x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; uint8_t x_206; 
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
x_206 = !lean_is_exclusive(x_158);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_158, 4);
lean_dec(x_207);
x_208 = lean_ctor_get(x_158, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_158, 2);
lean_dec(x_209);
x_210 = lean_ctor_get(x_158, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_158, 0);
lean_dec(x_211);
x_179 = x_158;
x_180 = x_206;
goto block_205;
}
else
{
lean_dec(x_158);
x_179 = lean_box(0);
x_180 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_194; 
x_181 = lean_nat_add(x_153, x_154);
x_182 = lean_nat_add(x_181, x_155);
lean_dec(x_155);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_173, 0);
lean_inc(x_203);
x_194 = x_203;
goto block_202;
}
else
{
lean_object* x_204; 
x_204 = lean_unsigned_to_nat(0u);
x_194 = x_204;
goto block_202;
}
block_193:
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_nat_add(x_184, x_185);
lean_dec(x_185);
lean_dec(x_184);
if (x_180 == 0)
{
lean_ctor_set(x_179, 4, x_159);
lean_ctor_set(x_179, 3, x_174);
lean_ctor_set(x_179, 2, x_157);
lean_ctor_set(x_179, 1, x_156);
lean_ctor_set(x_179, 0, x_186);
x_187 = x_179;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_186);
lean_ctor_set(x_192, 1, x_156);
lean_ctor_set(x_192, 2, x_157);
lean_ctor_set(x_192, 3, x_174);
lean_ctor_set(x_192, 4, x_159);
x_187 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_188; 
if (x_169 == 0)
{
lean_ctor_set(x_168, 4, x_187);
lean_ctor_set(x_168, 3, x_183);
lean_ctor_set(x_168, 2, x_172);
lean_ctor_set(x_168, 1, x_171);
lean_ctor_set(x_168, 0, x_182);
x_188 = x_168;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_171);
lean_ctor_set(x_190, 2, x_172);
lean_ctor_set(x_190, 3, x_183);
lean_ctor_set(x_190, 4, x_187);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
block_202:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_nat_add(x_181, x_194);
lean_dec(x_194);
lean_dec(x_181);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_173);
lean_ctor_set(x_9, 0, x_195);
x_196 = x_9;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_5);
lean_ctor_set(x_201, 2, x_6);
lean_ctor_set(x_201, 3, x_7);
lean_ctor_set(x_201, 4, x_173);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
x_197 = lean_nat_add(x_153, x_175);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_174, 0);
lean_inc(x_198);
x_183 = x_196;
x_184 = x_197;
x_185 = x_198;
goto block_193;
}
else
{
lean_object* x_199; 
x_199 = lean_unsigned_to_nat(0u);
x_183 = x_196;
x_184 = x_197;
x_185 = x_199;
goto block_193;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_del_object(x_9);
x_212 = lean_nat_add(x_153, x_154);
x_213 = lean_nat_add(x_212, x_155);
lean_dec(x_155);
x_214 = lean_nat_add(x_212, x_170);
lean_dec(x_212);
lean_inc_ref(x_7);
if (x_169 == 0)
{
lean_ctor_set(x_168, 4, x_158);
lean_ctor_set(x_168, 3, x_7);
lean_ctor_set(x_168, 2, x_6);
lean_ctor_set(x_168, 1, x_5);
lean_ctor_set(x_168, 0, x_214);
x_215 = x_168;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_214);
lean_ctor_set(x_229, 1, x_5);
lean_ctor_set(x_229, 2, x_6);
lean_ctor_set(x_229, 3, x_7);
lean_ctor_set(x_229, 4, x_158);
x_215 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_216; uint8_t x_217; uint8_t x_222; 
x_222 = !lean_is_exclusive(x_7);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_7, 4);
lean_dec(x_223);
x_224 = lean_ctor_get(x_7, 3);
lean_dec(x_224);
x_225 = lean_ctor_get(x_7, 2);
lean_dec(x_225);
x_226 = lean_ctor_get(x_7, 1);
lean_dec(x_226);
x_227 = lean_ctor_get(x_7, 0);
lean_dec(x_227);
x_216 = x_7;
x_217 = x_222;
goto block_221;
}
else
{
lean_dec(x_7);
x_216 = lean_box(0);
x_217 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_218; 
if (x_217 == 0)
{
lean_ctor_set(x_216, 4, x_159);
lean_ctor_set(x_216, 3, x_215);
lean_ctor_set(x_216, 2, x_157);
lean_ctor_set(x_216, 1, x_156);
lean_ctor_set(x_216, 0, x_213);
x_218 = x_216;
goto block_219;
}
else
{
lean_object* x_220; 
x_220 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_220, 0, x_213);
lean_ctor_set(x_220, 1, x_156);
lean_ctor_set(x_220, 2, x_157);
lean_ctor_set(x_220, 3, x_215);
lean_ctor_set(x_220, 4, x_159);
x_218 = x_220;
goto block_219;
}
block_219:
{
return x_218;
}
}
}
}
}
}
}
else
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_152, 3);
lean_inc(x_237);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_263; 
x_238 = lean_ctor_get(x_152, 4);
x_239 = lean_ctor_get(x_152, 1);
x_240 = lean_ctor_get(x_152, 2);
x_263 = !lean_is_exclusive(x_152);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_152, 3);
lean_dec(x_264);
x_265 = lean_ctor_get(x_152, 0);
lean_dec(x_265);
x_241 = x_152;
x_242 = x_263;
goto block_262;
}
else
{
lean_inc(x_238);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_152);
x_241 = lean_box(0);
x_242 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_258; 
x_243 = lean_ctor_get(x_237, 1);
x_244 = lean_ctor_get(x_237, 2);
x_258 = !lean_is_exclusive(x_237);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_237, 4);
lean_dec(x_259);
x_260 = lean_ctor_get(x_237, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_237, 0);
lean_dec(x_261);
x_245 = x_237;
x_246 = x_258;
goto block_257;
}
else
{
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_237);
x_245 = lean_box(0);
x_246 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_unsigned_to_nat(3u);
lean_inc_n(x_238, 2);
if (x_246 == 0)
{
lean_ctor_set(x_245, 4, x_238);
lean_ctor_set(x_245, 3, x_238);
lean_ctor_set(x_245, 2, x_6);
lean_ctor_set(x_245, 1, x_5);
lean_ctor_set(x_245, 0, x_153);
x_248 = x_245;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_256, 0, x_153);
lean_ctor_set(x_256, 1, x_5);
lean_ctor_set(x_256, 2, x_6);
lean_ctor_set(x_256, 3, x_238);
lean_ctor_set(x_256, 4, x_238);
x_248 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_249; 
lean_inc(x_238);
if (x_242 == 0)
{
lean_ctor_set(x_241, 3, x_238);
lean_ctor_set(x_241, 0, x_153);
x_249 = x_241;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_153);
lean_ctor_set(x_254, 1, x_239);
lean_ctor_set(x_254, 2, x_240);
lean_ctor_set(x_254, 3, x_238);
lean_ctor_set(x_254, 4, x_238);
x_249 = x_254;
goto block_253;
}
block_253:
{
lean_object* x_250; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_249);
lean_ctor_set(x_9, 3, x_248);
lean_ctor_set(x_9, 2, x_244);
lean_ctor_set(x_9, 1, x_243);
lean_ctor_set(x_9, 0, x_247);
x_250 = x_9;
goto block_251;
}
else
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_252, 0, x_247);
lean_ctor_set(x_252, 1, x_243);
lean_ctor_set(x_252, 2, x_244);
lean_ctor_set(x_252, 3, x_248);
lean_ctor_set(x_252, 4, x_249);
x_250 = x_252;
goto block_251;
}
block_251:
{
return x_250;
}
}
}
}
}
}
else
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_152, 4);
lean_inc(x_266);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_279; 
x_267 = lean_ctor_get(x_152, 1);
x_268 = lean_ctor_get(x_152, 2);
x_279 = !lean_is_exclusive(x_152);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_152, 4);
lean_dec(x_280);
x_281 = lean_ctor_get(x_152, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_152, 0);
lean_dec(x_282);
x_269 = x_152;
x_270 = x_279;
goto block_278;
}
else
{
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_152);
x_269 = lean_box(0);
x_270 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_unsigned_to_nat(3u);
if (x_270 == 0)
{
lean_ctor_set(x_269, 4, x_237);
lean_ctor_set(x_269, 2, x_6);
lean_ctor_set(x_269, 1, x_5);
lean_ctor_set(x_269, 0, x_153);
x_272 = x_269;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_277, 0, x_153);
lean_ctor_set(x_277, 1, x_5);
lean_ctor_set(x_277, 2, x_6);
lean_ctor_set(x_277, 3, x_237);
lean_ctor_set(x_277, 4, x_237);
x_272 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_273; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_266);
lean_ctor_set(x_9, 3, x_272);
lean_ctor_set(x_9, 2, x_268);
lean_ctor_set(x_9, 1, x_267);
lean_ctor_set(x_9, 0, x_271);
x_273 = x_9;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_275, 0, x_271);
lean_ctor_set(x_275, 1, x_267);
lean_ctor_set(x_275, 2, x_268);
lean_ctor_set(x_275, 3, x_272);
lean_ctor_set(x_275, 4, x_266);
x_273 = x_275;
goto block_274;
}
block_274:
{
return x_273;
}
}
}
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_unsigned_to_nat(2u);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_152);
lean_ctor_set(x_9, 3, x_266);
lean_ctor_set(x_9, 0, x_283);
x_284 = x_9;
goto block_285;
}
else
{
lean_object* x_286; 
x_286 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_5);
lean_ctor_set(x_286, 2, x_6);
lean_ctor_set(x_286, 3, x_266);
lean_ctor_set(x_286, 4, x_152);
x_284 = x_286;
goto block_285;
}
block_285:
{
return x_284;
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
lean_object* x_289; lean_object* x_290; 
x_289 = lean_unsigned_to_nat(1u);
x_290 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_1);
lean_ctor_set(x_290, 2, x_2);
lean_ctor_set(x_290, 3, x_3);
lean_ctor_set(x_290, 4, x_3);
return x_290;
}
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lake_LeanExe_defaultFacetConfig;
x_3 = l_Lake_LeanExe_defaultFacet;
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__0, &l_Lake_LeanExe_initFacetConfigs___closed__0_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__0);
x_2 = l_Lake_LeanExe_exeFacetConfig;
x_3 = l_Lake_LeanExe_exeFacet;
x_4 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanExe_initFacetConfigs(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lake_LeanExe_initFacetConfigs___closed__1, &l_Lake_LeanExe_initFacetConfigs___closed__1_once, _init_l_Lake_LeanExe_initFacetConfigs___closed__1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanExe_initFacetConfigs_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Executable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_FacetConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Register(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Target_Fetch(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Common(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13 = _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Executable_0__Lake_LeanExe_recBuildExe_spec__13);
l_Lake_LeanExe_exeFacetConfig = _init_l_Lake_LeanExe_exeFacetConfig();
lean_mark_persistent(l_Lake_LeanExe_exeFacetConfig);
l_Lake_LeanExe_defaultFacetConfig = _init_l_Lake_LeanExe_defaultFacetConfig();
lean_mark_persistent(l_Lake_LeanExe_defaultFacetConfig);
l_Lake_LeanExe_initFacetConfigs = _init_l_Lake_LeanExe_initFacetConfigs();
lean_mark_persistent(l_Lake_LeanExe_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Executable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* initialize_Lake_Build_Common(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Executable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Register(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Target_Fetch(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Executable(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Executable(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Executable(builtin);
}
#ifdef __cplusplus
}
#endif
