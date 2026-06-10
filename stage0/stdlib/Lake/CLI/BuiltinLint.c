// Lean compiler output
// Module: Lake.CLI.BuiltinLint
// Imports: public import Lean.Linter.EnvLinter public import Lean.Linter.PersistentLintLog import Lean.CoreM import Lake.Config.Workspace
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_get_stdout();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinters(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
lean_object* lean_compacted_region_free(size_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "weak"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 5, 49, 232, 223, 147, 119, 138)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lake_BuiltinLint_leanOptOverrides___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(size_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "-- Text linter diagnostics in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__8(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-- Linting passed for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "-- No environment linters were run for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__9;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__11;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__13;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__14;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__16_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__18_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__19;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__20;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__22_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__23_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__12_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__12_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__12___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_BuiltinLint_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "lake lint: no modules specified for builtin linting"};
static const lean_object* l_Lake_BuiltinLint_run___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_run___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(size_t v_sz_4_, size_t v_i_5_, lean_object* v_bs_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_lt(v_i_5_, v_sz_4_);
if (v___x_7_ == 0)
{
return v_bs_6_;
}
else
{
lean_object* v_v_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_27_; 
v_v_8_ = lean_array_uget(v_bs_6_, v_i_5_);
v_fst_9_ = lean_ctor_get(v_v_8_, 0);
v_snd_10_ = lean_ctor_get(v_v_8_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_v_8_);
if (v_isSharedCheck_27_ == 0)
{
v___x_12_ = v_v_8_;
v_isShared_13_ = v_isSharedCheck_27_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_snd_10_);
lean_inc(v_fst_9_);
lean_dec(v_v_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_27_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v_bs_x27_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_21_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v_bs_x27_15_ = lean_array_uset(v_bs_6_, v_i_5_, v___x_14_);
v___x_16_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___closed__1));
v___x_17_ = l_Lean_Name_append(v___x_16_, v_fst_9_);
v___x_18_ = lean_alloc_ctor(1, 0, 1);
v___x_19_ = lean_unbox(v_snd_10_);
lean_dec(v_snd_10_);
lean_ctor_set_uint8(v___x_18_, 0, v___x_19_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_18_);
lean_ctor_set(v___x_12_, 0, v___x_17_);
v___x_21_ = v___x_12_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_18_);
v___x_21_ = v_reuseFailAlloc_26_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
size_t v___x_22_; size_t v___x_23_; lean_object* v___x_24_; 
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_add(v_i_5_, v___x_22_);
v___x_24_ = lean_array_uset(v_bs_x27_15_, v_i_5_, v___x_21_);
v_i_5_ = v___x_23_;
v_bs_6_ = v___x_24_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1___boxed(lean_object* v_sz_28_, lean_object* v_i_29_, lean_object* v_bs_30_){
_start:
{
size_t v_sz_boxed_31_; size_t v_i_boxed_32_; lean_object* v_res_33_; 
v_sz_boxed_31_ = lean_unbox_usize(v_sz_28_);
lean_dec(v_sz_28_);
v_i_boxed_32_ = lean_unbox_usize(v_i_29_);
lean_dec(v_i_29_);
v_res_33_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_boxed_31_, v_i_boxed_32_, v_bs_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(lean_object* v_as_34_, size_t v_i_35_, size_t v_stop_36_, lean_object* v_b_37_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_usize_dec_eq(v_i_35_, v_stop_36_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v_fst_40_; lean_object* v_snd_41_; lean_object* v___x_42_; size_t v___x_43_; size_t v___x_44_; 
v___x_39_ = lean_array_uget_borrowed(v_as_34_, v_i_35_);
v_fst_40_ = lean_ctor_get(v___x_39_, 0);
v_snd_41_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_snd_41_);
lean_inc(v_fst_40_);
v___x_42_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_40_, v_snd_41_, v_b_37_);
v___x_43_ = ((size_t)1ULL);
v___x_44_ = lean_usize_add(v_i_35_, v___x_43_);
v_i_35_ = v___x_44_;
v_b_37_ = v___x_42_;
goto _start;
}
else
{
return v_b_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2___boxed(lean_object* v_as_46_, lean_object* v_i_47_, lean_object* v_stop_48_, lean_object* v_b_49_){
_start:
{
size_t v_i_boxed_50_; size_t v_stop_boxed_51_; lean_object* v_res_52_; 
v_i_boxed_50_ = lean_unbox_usize(v_i_47_);
lean_dec(v_i_47_);
v_stop_boxed_51_ = lean_unbox_usize(v_stop_48_);
lean_dec(v_stop_48_);
v_res_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_as_46_, v_i_boxed_50_, v_stop_boxed_51_, v_b_49_);
lean_dec_ref(v_as_46_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(lean_object* v_init_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v_k_55_; lean_object* v_v_56_; lean_object* v_l_57_; lean_object* v_r_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_k_55_ = lean_ctor_get(v_x_54_, 1);
v_v_56_ = lean_ctor_get(v_x_54_, 2);
v_l_57_ = lean_ctor_get(v_x_54_, 3);
v_r_58_ = lean_ctor_get(v_x_54_, 4);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_53_, v_l_57_);
lean_inc(v_v_56_);
lean_inc(v_k_55_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v_k_55_);
lean_ctor_set(v___x_60_, 1, v_v_56_);
v___x_61_ = lean_array_push(v___x_59_, v___x_60_);
v_init_53_ = v___x_61_;
v_x_54_ = v_r_58_;
goto _start;
}
else
{
return v_init_53_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0___boxed(lean_object* v_init_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_63_, v_x_64_);
lean_dec(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object* v_args_68_){
_start:
{
lean_object* v___y_70_; lean_object* v_linterOverrides_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_linterOverrides_77_ = lean_ctor_get(v_args_68_, 0);
v___x_78_ = lean_box(1);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_array_get_size(v_linterOverrides_77_);
v___x_81_ = lean_nat_dec_lt(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
v___y_70_ = v___x_78_;
goto v___jp_69_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = lean_nat_dec_le(v___x_80_, v___x_80_);
if (v___x_82_ == 0)
{
if (v___x_81_ == 0)
{
v___y_70_ = v___x_78_;
goto v___jp_69_;
}
else
{
size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; 
v___x_83_ = ((size_t)0ULL);
v___x_84_ = lean_usize_of_nat(v___x_80_);
v___x_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_77_, v___x_83_, v___x_84_, v___x_78_);
v___y_70_ = v___x_85_;
goto v___jp_69_;
}
}
else
{
size_t v___x_86_; size_t v___x_87_; lean_object* v___x_88_; 
v___x_86_ = ((size_t)0ULL);
v___x_87_ = lean_usize_of_nat(v___x_80_);
v___x_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_leanOptOverrides_spec__2(v_linterOverrides_77_, v___x_86_, v___x_87_, v___x_78_);
v___y_70_ = v___x_88_;
goto v___jp_69_;
}
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; size_t v_sz_73_; size_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_71_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__0));
v___x_72_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v___x_71_, v___y_70_);
lean_dec(v___y_70_);
v_sz_73_ = lean_array_size(v___x_72_);
v___x_74_ = ((size_t)0ULL);
v___x_75_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_BuiltinLint_leanOptOverrides_spec__1(v_sz_73_, v___x_74_, v___x_72_);
v___x_76_ = l_Lean_LeanOptions_ofArray(v___x_75_);
lean_dec_ref(v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object* v_args_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_89_);
lean_dec_ref(v_args_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(lean_object* v_init_91_, lean_object* v_t_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0_spec__0(v_init_91_, v_t_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0___boxed(lean_object* v_init_94_, lean_object* v_t_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lake_BuiltinLint_leanOptOverrides_spec__0(v_init_94_, v_t_95_);
lean_dec(v_t_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object* v_pkgRoot_97_, lean_object* v_as_98_, size_t v_i_99_, size_t v_stop_100_, lean_object* v_b_101_){
_start:
{
lean_object* v___y_103_; uint8_t v___x_107_; 
v___x_107_ = lean_usize_dec_eq(v_i_99_, v_stop_100_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; uint8_t v___y_110_; lean_object* v_fst_112_; lean_object* v_snd_113_; uint8_t v___x_114_; 
v___x_108_ = lean_array_uget_borrowed(v_as_98_, v_i_99_);
v_fst_112_ = lean_ctor_get(v___x_108_, 0);
v_snd_113_ = lean_ctor_get(v___x_108_, 1);
v___x_114_ = l_Lean_Name_isPrefixOf(v_pkgRoot_97_, v_fst_112_);
if (v___x_114_ == 0)
{
v___y_110_ = v___x_114_;
goto v___jp_109_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_array_get_size(v_snd_113_);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_dec_eq(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
v___y_110_ = v___x_114_;
goto v___jp_109_;
}
else
{
v___y_103_ = v_b_101_;
goto v___jp_102_;
}
}
v___jp_109_:
{
if (v___y_110_ == 0)
{
v___y_103_ = v_b_101_;
goto v___jp_102_;
}
else
{
lean_object* v___x_111_; 
lean_inc(v___x_108_);
v___x_111_ = lean_array_push(v_b_101_, v___x_108_);
v___y_103_ = v___x_111_;
goto v___jp_102_;
}
}
}
else
{
return v_b_101_;
}
v___jp_102_:
{
size_t v___x_104_; size_t v___x_105_; 
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_99_, v___x_104_);
v_i_99_ = v___x_105_;
v_b_101_ = v___y_103_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v_pkgRoot_118_, lean_object* v_as_119_, lean_object* v_i_120_, lean_object* v_stop_121_, lean_object* v_b_122_){
_start:
{
size_t v_i_boxed_123_; size_t v_stop_boxed_124_; lean_object* v_res_125_; 
v_i_boxed_123_ = lean_unbox_usize(v_i_120_);
lean_dec(v_i_120_);
v_stop_boxed_124_ = lean_unbox_usize(v_stop_121_);
lean_dec(v_stop_121_);
v_res_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_118_, v_as_119_, v_i_boxed_123_, v_stop_boxed_124_, v_b_122_);
lean_dec_ref(v_as_119_);
lean_dec(v_pkgRoot_118_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_128_, lean_object* v_pkgRoot_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_132_ = l_Lean_Linter_getAllLints(v_env_128_);
v___x_133_ = lean_array_get_size(v___x_132_);
v___x_134_ = lean_nat_dec_lt(v___x_130_, v___x_133_);
if (v___x_134_ == 0)
{
lean_dec_ref(v___x_132_);
return v___x_131_;
}
else
{
uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_le(v___x_133_, v___x_133_);
if (v___x_135_ == 0)
{
if (v___x_134_ == 0)
{
lean_dec_ref(v___x_132_);
return v___x_131_;
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_133_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_129_, v___x_132_, v___x_136_, v___x_137_, v___x_131_);
lean_dec_ref(v___x_132_);
return v___x_138_;
}
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_133_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_pkgRoot_129_, v___x_132_, v___x_139_, v___x_140_, v___x_131_);
lean_dec_ref(v___x_132_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_142_, lean_object* v_pkgRoot_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_142_, v_pkgRoot_143_);
lean_dec(v_pkgRoot_143_);
lean_dec_ref(v_env_142_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_145_){
_start:
{
uint8_t v_isModule_147_; 
v_isModule_147_ = lean_ctor_get_uint8(v_modData_145_, sizeof(void*)*5);
return v_isModule_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_148_, lean_object* v_a_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_148_);
lean_dec_ref(v_modData_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = lean_enable_initializer_execution();
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(size_t v_region_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_compacted_region_free(v_region_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_159_, lean_object* v_a_160_){
_start:
{
size_t v_region_boxed_161_; lean_object* v_res_162_; 
v_region_boxed_161_ = lean_unbox_usize(v_region_159_);
lean_dec(v_region_159_);
v_res_162_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_boxed_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_o_166_, lean_object* v_k_167_, uint8_t v_v_168_){
_start:
{
lean_object* v_map_169_; uint8_t v_hasTrace_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_184_; 
v_map_169_ = lean_ctor_get(v_o_166_, 0);
v_hasTrace_170_ = lean_ctor_get_uint8(v_o_166_, sizeof(void*)*1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_o_166_);
if (v_isSharedCheck_184_ == 0)
{
v___x_172_ = v_o_166_;
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_map_169_);
lean_dec(v_o_166_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_184_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_174_, 0, v_v_168_);
lean_inc(v_k_167_);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_167_, v___x_174_, v_map_169_);
if (v_hasTrace_170_ == 0)
{
lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_179_; 
v___x_176_ = ((lean_object*)(l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___closed__1));
v___x_177_ = l_Lean_Name_isPrefixOf(v___x_176_, v_k_167_);
lean_dec(v_k_167_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_179_ = v___x_172_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_175_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*1, v___x_177_);
return v___x_179_;
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v_k_167_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_175_);
v___x_182_ = v___x_172_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_175_);
lean_ctor_set_uint8(v_reuseFailAlloc_183_, sizeof(void*)*1, v_hasTrace_170_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_o_185_, lean_object* v_k_186_, lean_object* v_v_187_){
_start:
{
uint8_t v_v_boxed_188_; lean_object* v_res_189_; 
v_v_boxed_188_ = lean_unbox(v_v_187_);
v_res_189_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_o_185_, v_k_186_, v_v_boxed_188_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_s_190_){
_start:
{
lean_object* v___x_192_; lean_object* v_putStr_193_; lean_object* v___x_194_; 
v___x_192_ = lean_get_stdout();
v_putStr_193_ = lean_ctor_get(v___x_192_, 4);
lean_inc_ref(v_putStr_193_);
lean_dec_ref(v___x_192_);
v___x_194_ = lean_apply_2(v_putStr_193_, v_s_190_, lean_box(0));
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_s_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__2(v_s_195_);
return v_res_197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__6(lean_object* v_opts_198_, lean_object* v_opt_199_){
_start:
{
lean_object* v_name_200_; lean_object* v_defValue_201_; lean_object* v_map_202_; lean_object* v___x_203_; 
v_name_200_ = lean_ctor_get(v_opt_199_, 0);
v_defValue_201_ = lean_ctor_get(v_opt_199_, 1);
v_map_202_ = lean_ctor_get(v_opts_198_, 0);
v___x_203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_202_, v_name_200_);
if (lean_obj_tag(v___x_203_) == 0)
{
uint8_t v___x_204_; 
v___x_204_ = lean_unbox(v_defValue_201_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_203_, 1);
if (lean_obj_tag(v_val_205_) == 1)
{
uint8_t v_v_206_; 
v_v_206_ = lean_ctor_get_uint8(v_val_205_, 0);
lean_dec_ref_known(v_val_205_, 0);
return v_v_206_;
}
else
{
uint8_t v___x_207_; 
lean_dec(v_val_205_);
v___x_207_ = lean_unbox(v_defValue_201_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v_opts_208_, lean_object* v_opt_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__6(v_opts_208_, v_opt_209_);
lean_dec_ref(v_opt_209_);
lean_dec_ref(v_opts_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__7(lean_object* v_opts_212_, lean_object* v_opt_213_){
_start:
{
lean_object* v_name_214_; lean_object* v_defValue_215_; lean_object* v_map_216_; lean_object* v___x_217_; 
v_name_214_ = lean_ctor_get(v_opt_213_, 0);
v_defValue_215_ = lean_ctor_get(v_opt_213_, 1);
v_map_216_ = lean_ctor_get(v_opts_212_, 0);
v___x_217_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_216_, v_name_214_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_inc(v_defValue_215_);
return v_defValue_215_;
}
else
{
lean_object* v_val_218_; 
v_val_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_217_, 1);
if (lean_obj_tag(v_val_218_) == 3)
{
lean_object* v_v_219_; 
v_v_219_ = lean_ctor_get(v_val_218_, 0);
lean_inc(v_v_219_);
lean_dec_ref_known(v_val_218_, 1);
return v_v_219_;
}
else
{
lean_dec(v_val_218_);
lean_inc(v_defValue_215_);
return v_defValue_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object* v_opts_220_, lean_object* v_opt_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__7(v_opts_220_, v_opt_221_);
lean_dec_ref(v_opt_221_);
lean_dec_ref(v_opts_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3(lean_object* v_s_223_){
_start:
{
uint32_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = 10;
v___x_226_ = lean_string_push(v_s_223_, v___x_225_);
v___x_227_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__2(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v_s_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v_s_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(lean_object* v___x_231_, lean_object* v_as_232_, size_t v_sz_233_, size_t v_i_234_, lean_object* v_b_235_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_lt(v_i_234_, v_sz_233_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_b_235_);
return v___x_238_;
}
else
{
lean_object* v_a_239_; lean_object* v_message_240_; lean_object* v___x_241_; uint8_t v_anyFailed_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_239_ = lean_array_uget_borrowed(v_as_232_, v_i_234_);
v_message_240_ = lean_ctor_get(v_a_239_, 1);
v___x_241_ = lean_unsigned_to_nat(0u);
v_anyFailed_242_ = lean_nat_dec_eq(v___x_231_, v___x_241_);
lean_inc_ref(v_message_240_);
v___x_243_ = l_Lean_SerialMessage_toString(v_message_240_, v_anyFailed_242_);
v___x_244_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__2(v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v___x_245_; size_t v___x_246_; size_t v___x_247_; 
lean_dec_ref_known(v___x_244_, 1);
v___x_245_ = lean_box(0);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_add(v_i_234_, v___x_246_);
v_i_234_ = v___x_247_;
v_b_235_ = v___x_245_;
goto _start;
}
else
{
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v___x_249_, lean_object* v_as_250_, lean_object* v_sz_251_, lean_object* v_i_252_, lean_object* v_b_253_, lean_object* v___y_254_){
_start:
{
size_t v_sz_boxed_255_; size_t v_i_boxed_256_; lean_object* v_res_257_; 
v_sz_boxed_255_ = lean_unbox_usize(v_sz_251_);
lean_dec(v_sz_251_);
v_i_boxed_256_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(v___x_249_, v_as_250_, v_sz_boxed_255_, v_i_boxed_256_, v_b_253_);
lean_dec_ref(v_as_250_);
lean_dec(v___x_249_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v___x_260_, lean_object* v_as_261_, size_t v_sz_262_, size_t v_i_263_, lean_object* v_b_264_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_263_, v_sz_262_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_b_264_);
return v___x_267_;
}
else
{
lean_object* v_a_268_; lean_object* v_fst_269_; lean_object* v_snd_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_268_ = lean_array_uget_borrowed(v_as_261_, v_i_263_);
v_fst_269_ = lean_ctor_get(v_a_268_, 0);
v_snd_270_ = lean_ctor_get(v_a_268_, 1);
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0));
lean_inc(v_fst_269_);
v___x_272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_269_, v___x_266_);
v___x_273_ = lean_string_append(v___x_271_, v___x_272_);
lean_dec_ref(v___x_272_);
v___x_274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1));
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
v___x_276_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v___x_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; size_t v_sz_278_; size_t v___x_279_; lean_object* v___x_280_; 
lean_dec_ref_known(v___x_276_, 1);
v___x_277_ = lean_box(0);
v_sz_278_ = lean_array_size(v_snd_270_);
v___x_279_ = ((size_t)0ULL);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__4(v___x_260_, v_snd_270_, v_sz_278_, v___x_279_, v___x_277_);
if (lean_obj_tag(v___x_280_) == 0)
{
size_t v___x_281_; size_t v___x_282_; 
lean_dec_ref_known(v___x_280_, 1);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_add(v_i_263_, v___x_281_);
v_i_263_ = v___x_282_;
v_b_264_ = v___x_277_;
goto _start;
}
else
{
return v___x_280_;
}
}
else
{
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v___x_284_, lean_object* v_as_285_, lean_object* v_sz_286_, lean_object* v_i_287_, lean_object* v_b_288_, lean_object* v___y_289_){
_start:
{
size_t v_sz_boxed_290_; size_t v_i_boxed_291_; lean_object* v_res_292_; 
v_sz_boxed_290_ = lean_unbox_usize(v_sz_286_);
lean_dec(v_sz_286_);
v_i_boxed_291_ = lean_unbox_usize(v_i_287_);
lean_dec(v_i_287_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_284_, v_as_285_, v_sz_boxed_290_, v_i_boxed_291_, v_b_288_);
lean_dec_ref(v_as_285_);
lean_dec(v___x_284_);
return v_res_292_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__8(lean_object* v___x_293_, lean_object* v_as_294_, size_t v_i_295_, size_t v_stop_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_eq(v_i_295_, v_stop_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v_snd_299_; lean_object* v_size_300_; lean_object* v___x_301_; uint8_t v___x_302_; uint8_t v___x_303_; 
v___x_298_ = lean_array_uget_borrowed(v_as_294_, v_i_295_);
v_snd_299_ = lean_ctor_get(v___x_298_, 1);
v_size_300_ = lean_ctor_get(v_snd_299_, 0);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = 1;
v___x_303_ = lean_nat_dec_eq(v_size_300_, v___x_301_);
if (v___x_303_ == 0)
{
return v___x_302_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = lean_nat_dec_eq(v___x_293_, v___x_301_);
if (v___x_304_ == 0)
{
size_t v___x_305_; size_t v___x_306_; 
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_295_, v___x_305_);
v_i_295_ = v___x_306_;
goto _start;
}
else
{
return v___x_302_;
}
}
}
else
{
uint8_t v___x_308_; 
v___x_308_ = 0;
return v___x_308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object* v___x_309_, lean_object* v_as_310_, lean_object* v_i_311_, lean_object* v_stop_312_){
_start:
{
size_t v_i_boxed_313_; size_t v_stop_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_i_boxed_313_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_stop_boxed_314_ = lean_unbox_usize(v_stop_312_);
lean_dec(v_stop_312_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__8(v___x_309_, v_as_310_, v_i_boxed_313_, v_stop_boxed_314_);
lean_dec_ref(v_as_310_);
lean_dec(v___x_309_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__10(lean_object* v_as_317_, size_t v_i_318_, size_t v_stop_319_, lean_object* v_b_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_eq(v_i_318_, v_stop_319_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v_fst_323_; lean_object* v_snd_324_; uint8_t v___x_325_; lean_object* v___x_326_; size_t v___x_327_; size_t v___x_328_; 
v___x_322_ = lean_array_uget_borrowed(v_as_317_, v_i_318_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
v_snd_324_ = lean_ctor_get(v___x_322_, 1);
v___x_325_ = lean_unbox(v_snd_324_);
lean_inc(v_fst_323_);
v___x_326_ = l_Lean_Options_set___at___00Lake_BuiltinLint_run_spec__0(v_b_320_, v_fst_323_, v___x_325_);
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_add(v_i_318_, v___x_327_);
v_i_318_ = v___x_328_;
v_b_320_ = v___x_326_;
goto _start;
}
else
{
return v_b_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__10___boxed(lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_stop_332_, lean_object* v_b_333_){
_start:
{
size_t v_i_boxed_334_; size_t v_stop_boxed_335_; lean_object* v_res_336_; 
v_i_boxed_334_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_stop_boxed_335_ = lean_unbox_usize(v_stop_332_);
lean_dec(v_stop_332_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__10(v_as_330_, v_i_boxed_334_, v_stop_boxed_335_, v_b_333_);
lean_dec_ref(v_as_330_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(lean_object* v___x_337_, lean_object* v_as_338_, size_t v_i_339_, size_t v_stop_340_, lean_object* v_b_341_){
_start:
{
lean_object* v___y_343_; uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_eq(v_i_339_, v_stop_340_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v_linter_349_; uint8_t v___x_350_; 
v___x_348_ = lean_array_uget_borrowed(v_as_338_, v_i_339_);
v_linter_349_ = lean_ctor_get(v___x_348_, 0);
v___x_350_ = l_Lean_Linter_isLinterEnabledByOptions(v_linter_349_, v___x_337_);
if (v___x_350_ == 0)
{
v___y_343_ = v_b_341_;
goto v___jp_342_;
}
else
{
lean_object* v___x_351_; 
lean_inc(v___x_348_);
v___x_351_ = lean_array_push(v_b_341_, v___x_348_);
v___y_343_ = v___x_351_;
goto v___jp_342_;
}
}
else
{
return v_b_341_;
}
v___jp_342_:
{
size_t v___x_344_; size_t v___x_345_; 
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_add(v_i_339_, v___x_344_);
v_i_339_ = v___x_345_;
v_b_341_ = v___y_343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v___x_352_, lean_object* v_as_353_, lean_object* v_i_354_, lean_object* v_stop_355_, lean_object* v_b_356_){
_start:
{
size_t v_i_boxed_357_; size_t v_stop_boxed_358_; lean_object* v_res_359_; 
v_i_boxed_357_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_stop_boxed_358_ = lean_unbox_usize(v_stop_355_);
lean_dec(v_stop_355_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_352_, v_as_353_, v_i_boxed_357_, v_stop_boxed_358_, v_b_356_);
lean_dec_ref(v_as_353_);
lean_dec_ref(v___x_352_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9(lean_object* v___x_362_, lean_object* v_as_363_, size_t v_i_364_, size_t v_stop_365_, lean_object* v_b_366_){
_start:
{
lean_object* v___y_368_; uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_eq(v_i_364_, v_stop_365_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v_fst_374_; lean_object* v_snd_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_398_; 
v___x_373_ = lean_array_uget(v_as_363_, v_i_364_);
v_fst_374_ = lean_ctor_get(v___x_373_, 0);
v_snd_375_ = lean_ctor_get(v___x_373_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_398_ == 0)
{
v___x_377_ = v___x_373_;
v_isShared_378_ = v_isSharedCheck_398_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_snd_375_);
lean_inc(v_fst_374_);
lean_dec(v___x_373_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_398_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___y_381_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_array_get_size(v_snd_375_);
v___x_389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9___closed__0));
v___x_390_ = lean_nat_dec_lt(v___x_379_, v___x_388_);
if (v___x_390_ == 0)
{
lean_dec(v_snd_375_);
v___y_381_ = v___x_389_;
goto v___jp_380_;
}
else
{
uint8_t v___x_391_; 
v___x_391_ = lean_nat_dec_le(v___x_388_, v___x_388_);
if (v___x_391_ == 0)
{
if (v___x_390_ == 0)
{
lean_dec(v_snd_375_);
v___y_381_ = v___x_389_;
goto v___jp_380_;
}
else
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((size_t)0ULL);
v___x_393_ = lean_usize_of_nat(v___x_388_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_362_, v_snd_375_, v___x_392_, v___x_393_, v___x_389_);
lean_dec(v_snd_375_);
v___y_381_ = v___x_394_;
goto v___jp_380_;
}
}
else
{
size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; 
v___x_395_ = ((size_t)0ULL);
v___x_396_ = lean_usize_of_nat(v___x_388_);
v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__1(v___x_362_, v_snd_375_, v___x_395_, v___x_396_, v___x_389_);
lean_dec(v_snd_375_);
v___y_381_ = v___x_397_;
goto v___jp_380_;
}
}
v___jp_380_:
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_array_get_size(v___y_381_);
v___x_383_ = lean_nat_dec_eq(v___x_382_, v___x_379_);
if (v___x_383_ == 0)
{
lean_object* v___x_385_; 
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v___y_381_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_fst_374_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___y_381_);
v___x_385_ = v_reuseFailAlloc_387_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = lean_array_push(v_b_366_, v___x_385_);
v___y_368_ = v___x_386_;
goto v___jp_367_;
}
}
else
{
lean_dec_ref(v___y_381_);
lean_del_object(v___x_377_);
lean_dec(v_fst_374_);
v___y_368_ = v_b_366_;
goto v___jp_367_;
}
}
}
}
else
{
return v_b_366_;
}
v___jp_367_:
{
size_t v___x_369_; size_t v___x_370_; 
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_364_, v___x_369_);
v_i_364_ = v___x_370_;
v_b_366_ = v___y_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9___boxed(lean_object* v___x_399_, lean_object* v_as_400_, lean_object* v_i_401_, lean_object* v_stop_402_, lean_object* v_b_403_){
_start:
{
size_t v_i_boxed_404_; size_t v_stop_boxed_405_; lean_object* v_res_406_; 
v_i_boxed_404_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_stop_boxed_405_ = lean_unbox_usize(v_stop_402_);
lean_dec(v_stop_402_);
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9(v___x_399_, v_as_400_, v_i_boxed_404_, v_stop_boxed_405_, v_b_403_);
lean_dec_ref(v_as_400_);
lean_dec_ref(v___x_399_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9(lean_object* v___x_407_, lean_object* v_as_408_, lean_object* v_start_409_, lean_object* v_stop_410_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_412_ = lean_nat_dec_lt(v_start_409_, v_stop_410_);
if (v___x_412_ == 0)
{
return v___x_411_;
}
else
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_array_get_size(v_as_408_);
v___x_414_ = lean_nat_dec_le(v_stop_410_, v___x_413_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = lean_nat_dec_lt(v_start_409_, v___x_413_);
if (v___x_415_ == 0)
{
return v___x_411_;
}
else
{
size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_usize_of_nat(v_start_409_);
v___x_417_ = lean_usize_of_nat(v___x_413_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9(v___x_407_, v_as_408_, v___x_416_, v___x_417_, v___x_411_);
return v___x_418_;
}
}
else
{
size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_usize_of_nat(v_start_409_);
v___x_420_ = lean_usize_of_nat(v_stop_410_);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9_spec__9(v___x_407_, v_as_408_, v___x_419_, v___x_420_, v___x_411_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9___boxed(lean_object* v___x_422_, lean_object* v_as_423_, lean_object* v_start_424_, lean_object* v_stop_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9(v___x_422_, v_as_423_, v_start_424_, v_stop_425_);
lean_dec(v_stop_425_);
lean_dec(v_start_424_);
lean_dec_ref(v_as_423_);
lean_dec_ref(v___x_422_);
return v_res_426_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__9(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(32u);
v___x_440_ = lean_mk_empty_array_with_capacity(v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10(void){
_start:
{
size_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_442_ = ((size_t)5ULL);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_unsigned_to_nat(32u);
v___x_445_ = lean_mk_empty_array_with_capacity(v___x_444_);
v___x_446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__9);
v___x_447_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_443_);
lean_ctor_set(v___x_447_, 3, v___x_443_);
lean_ctor_set_usize(v___x_447_, 4, v___x_442_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__11(void){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_448_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__11);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__13(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__14(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = l_Lean_NameSet_empty;
v___x_454_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
lean_ctor_set(v___x_455_, 2, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__15(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = l_Lean_firstFrontendMacroScope;
v___x_458_ = lean_nat_add(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__19(void){
_start:
{
lean_object* v___x_465_; uint64_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10);
v___x_466_ = 0ULL;
v___x_467_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set_uint64(v___x_467_, sizeof(void*)*1, v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__20(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v_anyFailed_470_; lean_object* v___x_471_; 
v___x_468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__10);
v___x_469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__12);
v_anyFailed_470_ = 1;
v___x_471_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
lean_ctor_set(v___x_471_, 2, v___x_468_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*3, v_anyFailed_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(lean_object* v___x_477_, lean_object* v_args_478_, lean_object* v_as_479_, size_t v_sz_480_, size_t v_i_481_, uint8_t v_b_482_){
_start:
{
uint8_t v_a_485_; lean_object* v_msg_490_; lean_object* v_a_495_; lean_object* v___x_503_; uint8_t v_anyFailed_504_; uint8_t v_anyFailed_505_; uint8_t v___y_507_; lean_object* v___y_508_; uint8_t v_a_509_; lean_object* v___x_511_; lean_object* v_envLinterModule_512_; uint8_t v___x_513_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v_anyFailed_504_ = lean_nat_dec_eq(v___x_477_, v___x_503_);
v_anyFailed_505_ = 1;
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__4));
v_envLinterModule_512_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_512_, 0, v___x_511_);
lean_ctor_set_uint8(v_envLinterModule_512_, sizeof(void*)*1, v_anyFailed_504_);
lean_ctor_set_uint8(v_envLinterModule_512_, sizeof(void*)*1 + 1, v_anyFailed_505_);
lean_ctor_set_uint8(v_envLinterModule_512_, sizeof(void*)*1 + 2, v_anyFailed_504_);
v___x_513_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref_known(v_envLinterModule_512_, 1);
v___x_514_ = lean_box(v_b_482_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; uint8_t v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; uint8_t v___y_526_; uint8_t v___y_563_; size_t v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; uint8_t v___y_599_; uint8_t v___y_600_; size_t v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; uint8_t v___y_645_; uint8_t v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; size_t v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; uint8_t v___y_655_; lean_object* v___y_676_; uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; uint8_t v___y_683_; uint8_t v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; uint8_t v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___x_758_; 
lean_dec_ref_known(v___x_516_, 1);
v_a_517_ = lean_array_uget_borrowed(v_as_479_, v_i_481_);
lean_inc(v_a_517_);
v___x_758_ = l_Lean_findOLean(v_a_517_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = l_Lean_readModuleData(v_a_759_);
lean_dec(v_a_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v_fst_762_; lean_object* v_snd_763_; uint8_t v___x_764_; uint8_t v___y_766_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v_fst_762_ = lean_ctor_get(v_a_761_, 0);
lean_inc(v_fst_762_);
v_snd_763_ = lean_ctor_get(v_a_761_, 1);
lean_inc(v_snd_763_);
lean_dec(v_a_761_);
v___x_764_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_762_);
lean_dec(v_fst_762_);
if (v___x_764_ == 0)
{
uint8_t v___x_807_; 
v___x_807_ = 2;
v___y_766_ = v___x_807_;
goto v___jp_765_;
}
else
{
uint8_t v___x_808_; 
v___x_808_ = 0;
v___y_766_ = v___x_808_;
goto v___jp_765_;
}
v___jp_765_:
{
size_t v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unbox_usize(v_snd_763_);
lean_dec(v_snd_763_);
v___x_768_ = lean_compacted_region_free(v___x_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint32_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref_known(v___x_768_, 1);
lean_inc(v_a_517_);
v___x_769_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_769_, 0, v_a_517_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v_anyFailed_504_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1 + 1, v_anyFailed_505_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1 + 2, v_anyFailed_504_);
v___x_770_ = lean_unsigned_to_nat(2u);
v___x_771_ = lean_mk_empty_array_with_capacity(v___x_770_);
v___x_772_ = lean_array_push(v___x_771_, v___x_769_);
v___x_773_ = lean_array_push(v___x_772_, v_envLinterModule_512_);
v___x_774_ = l_Lean_Options_empty;
v___x_775_ = 1024;
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__23));
v___x_777_ = lean_box(1);
v___x_778_ = l_Lean_importModules(v___x_773_, v___x_774_, v___x_775_, v___x_776_, v_anyFailed_504_, v_anyFailed_505_, v___y_766_, v___x_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v_linterOverrides_780_; uint8_t v_lintOnly_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v_linterOverrides_780_ = lean_ctor_get(v_args_478_, 0);
v_lintOnly_781_ = lean_ctor_get_uint8(v_args_478_, sizeof(void*)*2);
v___x_782_ = lean_array_get_size(v_linterOverrides_780_);
v___x_783_ = lean_nat_dec_lt(v___x_503_, v___x_782_);
if (v___x_783_ == 0)
{
v___y_735_ = v_lintOnly_781_;
v___y_736_ = v___x_774_;
v___y_737_ = v_a_779_;
v___y_738_ = v___x_774_;
goto v___jp_734_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___x_782_, v___x_782_);
if (v___x_784_ == 0)
{
if (v___x_783_ == 0)
{
v___y_735_ = v_lintOnly_781_;
v___y_736_ = v___x_774_;
v___y_737_ = v_a_779_;
v___y_738_ = v___x_774_;
goto v___jp_734_;
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_782_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__10(v_linterOverrides_780_, v___x_785_, v___x_786_, v___x_774_);
v___y_735_ = v_lintOnly_781_;
v___y_736_ = v___x_774_;
v___y_737_ = v_a_779_;
v___y_738_ = v___x_787_;
goto v___jp_734_;
}
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_782_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_BuiltinLint_run_spec__10(v_linterOverrides_780_, v___x_788_, v___x_789_, v___x_774_);
v___y_735_ = v_lintOnly_781_;
v___y_736_ = v___x_774_;
v___y_737_ = v_a_779_;
v___y_738_ = v___x_790_;
goto v___jp_734_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_778_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_778_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref_known(v_envLinterModule_512_, 1);
v_a_799_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_768_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_768_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref_known(v_envLinterModule_512_, 1);
v_a_809_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_760_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_760_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref_known(v_envLinterModule_512_, 1);
v_a_817_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_758_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_758_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
v___jp_518_:
{
if (v___y_526_ == 0)
{
lean_dec(v___y_525_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
if (v___y_519_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__5));
lean_inc(v_a_517_);
v___x_528_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_517_, v_anyFailed_505_);
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
lean_dec_ref(v___x_528_);
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__6));
v___x_531_ = lean_string_append(v___x_529_, v___x_530_);
v___x_532_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v___x_531_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_dec_ref_known(v___x_532_, 1);
v___y_507_ = v___y_519_;
v___y_508_ = v___y_524_;
v_a_509_ = v___y_526_;
goto v___jp_506_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
lean_dec(v___y_524_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_542_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_io_error_to_string(v_a_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 3);
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_541_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_MessageData_ofFormat(v___x_539_);
v_msg_490_ = v___x_540_;
goto v___jp_489_;
}
}
}
}
else
{
v___y_507_ = v___y_519_;
v___y_508_ = v___y_524_;
v_a_509_ = v___y_526_;
goto v___jp_506_;
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; 
v___x_543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__7));
lean_inc(v_a_517_);
v___x_544_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_517_, v___y_526_);
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
lean_dec_ref(v___x_544_);
v___x_546_ = 1;
v___x_547_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_522_, v___y_523_, v_anyFailed_505_, v___x_545_, v___x_546_, v___y_520_, v_anyFailed_505_, v___y_521_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_523_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = l_Lean_MessageData_toString(v_a_548_);
v___x_550_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__2(v___x_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_dec_ref_known(v___x_550_, 1);
v___y_507_ = v___y_519_;
v___y_508_ = v___y_524_;
v_a_509_ = v___y_526_;
goto v___jp_506_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_560_; 
lean_dec(v___y_524_);
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_560_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_io_error_to_string(v_a_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set_tag(v___x_553_, 3);
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_MessageData_ofFormat(v___x_557_);
v_msg_490_ = v___x_558_;
goto v___jp_489_;
}
}
}
}
else
{
lean_object* v_a_561_; 
lean_dec(v___y_524_);
v_a_561_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_547_, 1);
v_a_495_ = v_a_561_;
goto v___jp_494_;
}
}
}
v___jp_562_:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Linter_EnvLinter_getEnvLinters(v___y_569_, v___y_565_, v___y_568_);
lean_dec(v___y_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = lean_array_get_size(v_a_571_);
v___x_573_ = lean_nat_dec_eq(v___x_572_, v___x_503_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Linter_EnvLinter_lintCore(v___y_566_, v_a_571_, v___y_565_, v___y_568_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_array_get_size(v_a_575_);
v___x_577_ = lean_nat_dec_lt(v___x_503_, v___x_576_);
if (v___x_577_ == 0)
{
v___y_519_ = v___y_563_;
v___y_520_ = v___x_572_;
v___y_521_ = v___y_565_;
v___y_522_ = v_a_575_;
v___y_523_ = v___y_566_;
v___y_524_ = v___y_567_;
v___y_525_ = v___y_568_;
v___y_526_ = v___x_573_;
goto v___jp_518_;
}
else
{
if (v___x_577_ == 0)
{
v___y_519_ = v___y_563_;
v___y_520_ = v___x_572_;
v___y_521_ = v___y_565_;
v___y_522_ = v_a_575_;
v___y_523_ = v___y_566_;
v___y_524_ = v___y_567_;
v___y_525_ = v___y_568_;
v___y_526_ = v___x_573_;
goto v___jp_518_;
}
else
{
size_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_usize_of_nat(v___x_576_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__8(v___x_572_, v_a_575_, v___y_564_, v___x_578_);
v___y_519_ = v___y_563_;
v___y_520_ = v___x_572_;
v___y_521_ = v___y_565_;
v___y_522_ = v_a_575_;
v___y_523_ = v___y_566_;
v___y_524_ = v___y_567_;
v___y_525_ = v___y_568_;
v___y_526_ = v___x_579_;
goto v___jp_518_;
}
}
}
else
{
lean_object* v_a_580_; 
lean_dec(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v___y_565_);
v_a_580_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_574_, 1);
v_a_495_ = v_a_580_;
goto v___jp_494_;
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v_a_571_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v___y_565_);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__8));
lean_inc(v_a_517_);
v___x_582_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_517_, v___x_573_);
v___x_583_ = lean_string_append(v___x_581_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__6));
v___x_585_ = lean_string_append(v___x_583_, v___x_584_);
v___x_586_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__3(v___x_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_dec_ref_known(v___x_586_, 1);
v___y_507_ = v___y_563_;
v___y_508_ = v___y_567_;
v_a_509_ = v_anyFailed_504_;
goto v___jp_506_;
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_596_; 
lean_dec(v___y_567_);
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_596_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_596_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_596_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_io_error_to_string(v_a_587_);
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 3);
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_595_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_MessageData_ofFormat(v___x_593_);
v_msg_490_ = v___x_594_;
goto v___jp_489_;
}
}
}
}
}
else
{
lean_object* v_a_597_; 
lean_dec(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v___y_565_);
v_a_597_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_570_, 1);
v_a_495_ = v_a_597_;
goto v___jp_494_;
}
}
v___jp_598_:
{
lean_object* v_fileName_609_; lean_object* v_fileMap_610_; lean_object* v_currRecDepth_611_; lean_object* v_ref_612_; lean_object* v_currNamespace_613_; lean_object* v_openDecls_614_; lean_object* v_initHeartbeats_615_; lean_object* v_maxHeartbeats_616_; lean_object* v_quotContext_617_; lean_object* v_currMacroScope_618_; lean_object* v_cancelTk_x3f_619_; uint8_t v_suppressElabErrors_620_; lean_object* v_inheritedTraceOptions_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_641_; 
v_fileName_609_ = lean_ctor_get(v___y_607_, 0);
v_fileMap_610_ = lean_ctor_get(v___y_607_, 1);
v_currRecDepth_611_ = lean_ctor_get(v___y_607_, 3);
v_ref_612_ = lean_ctor_get(v___y_607_, 5);
v_currNamespace_613_ = lean_ctor_get(v___y_607_, 6);
v_openDecls_614_ = lean_ctor_get(v___y_607_, 7);
v_initHeartbeats_615_ = lean_ctor_get(v___y_607_, 8);
v_maxHeartbeats_616_ = lean_ctor_get(v___y_607_, 9);
v_quotContext_617_ = lean_ctor_get(v___y_607_, 10);
v_currMacroScope_618_ = lean_ctor_get(v___y_607_, 11);
v_cancelTk_x3f_619_ = lean_ctor_get(v___y_607_, 12);
v_suppressElabErrors_620_ = lean_ctor_get_uint8(v___y_607_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_621_ = lean_ctor_get(v___y_607_, 13);
v_isSharedCheck_641_ = !lean_is_exclusive(v___y_607_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; 
v_unused_642_ = lean_ctor_get(v___y_607_, 4);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v___y_607_, 2);
lean_dec(v_unused_643_);
v___x_623_ = v___y_607_;
v_isShared_624_ = v_isSharedCheck_641_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_inheritedTraceOptions_621_);
lean_inc(v_cancelTk_x3f_619_);
lean_inc(v_currMacroScope_618_);
lean_inc(v_quotContext_617_);
lean_inc(v_maxHeartbeats_616_);
lean_inc(v_initHeartbeats_615_);
lean_inc(v_openDecls_614_);
lean_inc(v_currNamespace_613_);
lean_inc(v_ref_612_);
lean_inc(v_currRecDepth_611_);
lean_inc(v_fileMap_610_);
lean_inc(v_fileName_609_);
lean_dec(v___y_607_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_641_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___y_602_, v___y_608_);
lean_dec(v___y_602_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_639_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_639_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_630_ = l_Lean_maxRecDepth;
v___x_631_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__7(v___y_605_, v___x_630_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v___x_631_);
lean_ctor_set(v___x_623_, 2, v___y_605_);
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_fileName_609_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_fileMap_610_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v___y_605_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_currRecDepth_611_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_638_, 5, v_ref_612_);
lean_ctor_set(v_reuseFailAlloc_638_, 6, v_currNamespace_613_);
lean_ctor_set(v_reuseFailAlloc_638_, 7, v_openDecls_614_);
lean_ctor_set(v_reuseFailAlloc_638_, 8, v_initHeartbeats_615_);
lean_ctor_set(v_reuseFailAlloc_638_, 9, v_maxHeartbeats_616_);
lean_ctor_set(v_reuseFailAlloc_638_, 10, v_quotContext_617_);
lean_ctor_set(v_reuseFailAlloc_638_, 11, v_currMacroScope_618_);
lean_ctor_set(v_reuseFailAlloc_638_, 12, v_cancelTk_x3f_619_);
lean_ctor_set(v_reuseFailAlloc_638_, 13, v_inheritedTraceOptions_621_);
lean_ctor_set_uint8(v_reuseFailAlloc_638_, sizeof(void*)*14 + 1, v_suppressElabErrors_620_);
v___x_633_ = v_reuseFailAlloc_638_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*14, v___y_603_);
if (v___y_600_ == 0)
{
lean_object* v___x_634_; 
lean_del_object(v___x_628_);
lean_dec_ref(v___y_606_);
v___x_634_ = lean_box(0);
v___y_563_ = v___y_599_;
v___y_564_ = v___y_601_;
v___y_565_ = v___x_633_;
v___y_566_ = v_a_626_;
v___y_567_ = v___y_604_;
v___y_568_ = v___y_608_;
v___y_569_ = v___x_634_;
goto v___jp_562_;
}
else
{
lean_object* v___x_636_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 1);
lean_ctor_set(v___x_628_, 0, v___y_606_);
v___x_636_ = v___x_628_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___y_606_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
v___y_563_ = v___y_599_;
v___y_564_ = v___y_601_;
v___y_565_ = v___x_633_;
v___y_566_ = v_a_626_;
v___y_567_ = v___y_604_;
v___y_568_ = v___y_608_;
v___y_569_ = v___x_636_;
goto v___jp_562_;
}
}
}
}
}
else
{
lean_object* v_a_640_; 
lean_del_object(v___x_623_);
lean_dec_ref(v_inheritedTraceOptions_621_);
lean_dec(v_cancelTk_x3f_619_);
lean_dec(v_currMacroScope_618_);
lean_dec(v_quotContext_617_);
lean_dec(v_maxHeartbeats_616_);
lean_dec(v_initHeartbeats_615_);
lean_dec(v_openDecls_614_);
lean_dec(v_currNamespace_613_);
lean_dec(v_ref_612_);
lean_dec(v_currRecDepth_611_);
lean_dec_ref(v_fileMap_610_);
lean_dec_ref(v_fileName_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
v_a_640_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_625_, 1);
v_a_495_ = v_a_640_;
goto v___jp_494_;
}
}
}
v___jp_644_:
{
if (v___y_655_ == 0)
{
lean_object* v___x_656_; lean_object* v_env_657_; lean_object* v_nextMacroScope_658_; lean_object* v_ngen_659_; lean_object* v_auxDeclNGen_660_; lean_object* v_traceState_661_; lean_object* v_messages_662_; lean_object* v_infoState_663_; lean_object* v_snapshotTasks_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_673_; 
v___x_656_ = lean_st_ref_take(v___y_653_);
v_env_657_ = lean_ctor_get(v___x_656_, 0);
v_nextMacroScope_658_ = lean_ctor_get(v___x_656_, 1);
v_ngen_659_ = lean_ctor_get(v___x_656_, 2);
v_auxDeclNGen_660_ = lean_ctor_get(v___x_656_, 3);
v_traceState_661_ = lean_ctor_get(v___x_656_, 4);
v_messages_662_ = lean_ctor_get(v___x_656_, 6);
v_infoState_663_ = lean_ctor_get(v___x_656_, 7);
v_snapshotTasks_664_ = lean_ctor_get(v___x_656_, 8);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_656_, 5);
lean_dec(v_unused_674_);
v___x_666_ = v___x_656_;
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_snapshotTasks_664_);
lean_inc(v_infoState_663_);
lean_inc(v_messages_662_);
lean_inc(v_traceState_661_);
lean_inc(v_auxDeclNGen_660_);
lean_inc(v_ngen_659_);
lean_inc(v_nextMacroScope_658_);
lean_inc(v_env_657_);
lean_dec(v___x_656_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_Lean_Kernel_enableDiag(v_env_657_, v___y_650_);
lean_inc_ref(v___y_647_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 5, v___y_647_);
lean_ctor_set(v___x_666_, 0, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_nextMacroScope_658_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_ngen_659_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_auxDeclNGen_660_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_traceState_661_);
lean_ctor_set(v_reuseFailAlloc_672_, 5, v___y_647_);
lean_ctor_set(v_reuseFailAlloc_672_, 6, v_messages_662_);
lean_ctor_set(v_reuseFailAlloc_672_, 7, v_infoState_663_);
lean_ctor_set(v_reuseFailAlloc_672_, 8, v_snapshotTasks_664_);
v___x_670_ = v_reuseFailAlloc_672_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_st_ref_set(v___y_653_, v___x_670_);
lean_inc(v___y_653_);
v___y_599_ = v___y_645_;
v___y_600_ = v___y_646_;
v___y_601_ = v___y_649_;
v___y_602_ = v___y_648_;
v___y_603_ = v___y_650_;
v___y_604_ = v___y_653_;
v___y_605_ = v___y_652_;
v___y_606_ = v___y_654_;
v___y_607_ = v___y_651_;
v___y_608_ = v___y_653_;
goto v___jp_598_;
}
}
}
else
{
lean_inc(v___y_653_);
v___y_599_ = v___y_645_;
v___y_600_ = v___y_646_;
v___y_601_ = v___y_649_;
v___y_602_ = v___y_648_;
v___y_603_ = v___y_650_;
v___y_604_ = v___y_653_;
v___y_605_ = v___y_652_;
v___y_606_ = v___y_654_;
v___y_607_ = v___y_651_;
v___y_608_ = v___y_653_;
goto v___jp_598_;
}
}
v___jp_675_:
{
lean_object* v___x_684_; size_t v_sz_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_box(0);
v_sz_685_ = lean_array_size(v___y_676_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_477_, v___y_676_, v_sz_685_, v___x_686_, v___x_684_);
lean_dec_ref(v___y_676_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_env_712_; lean_object* v___x_713_; uint8_t v___x_714_; uint8_t v___x_715_; 
lean_dec_ref_known(v___x_687_, 1);
v___x_688_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__13);
v___x_689_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__14);
v___x_690_ = lean_io_get_num_heartbeats();
v___x_691_ = l_Lean_firstFrontendMacroScope;
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__15);
v___x_694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__18));
v___x_695_ = lean_box(0);
lean_inc_n(v___y_682_, 2);
v___x_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_696_, 0, v___y_682_);
lean_ctor_set(v___x_696_, 1, v___x_692_);
lean_ctor_set(v___x_696_, 2, v___x_695_);
v___x_697_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__19, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__19_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__19);
v___x_698_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__20);
v___x_699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__21));
v___x_700_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_700_, 0, v___y_680_);
lean_ctor_set(v___x_700_, 1, v___x_693_);
lean_ctor_set(v___x_700_, 2, v___x_694_);
lean_ctor_set(v___x_700_, 3, v___x_696_);
lean_ctor_set(v___x_700_, 4, v___x_697_);
lean_ctor_set(v___x_700_, 5, v___x_688_);
lean_ctor_set(v___x_700_, 6, v___x_689_);
lean_ctor_set(v___x_700_, 7, v___x_698_);
lean_ctor_set(v___x_700_, 8, v___x_699_);
v___x_701_ = lean_st_mk_ref(v___x_700_);
v___x_702_ = l_Lean_inheritedTraceOptions;
v___x_703_ = lean_st_ref_get(v___x_702_);
v___x_704_ = lean_st_ref_get(v___x_701_);
v___x_705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__22));
v___x_706_ = l_Lean_instInhabitedFileMap_default;
v___x_707_ = lean_unsigned_to_nat(1000u);
v___x_708_ = lean_box(0);
v___x_709_ = l_Lean_Core_getMaxHeartbeats(v___y_679_);
v___x_710_ = lean_box(0);
lean_inc_ref(v___y_679_);
v___x_711_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_711_, 0, v___x_705_);
lean_ctor_set(v___x_711_, 1, v___x_706_);
lean_ctor_set(v___x_711_, 2, v___y_679_);
lean_ctor_set(v___x_711_, 3, v___x_503_);
lean_ctor_set(v___x_711_, 4, v___x_707_);
lean_ctor_set(v___x_711_, 5, v___x_708_);
lean_ctor_set(v___x_711_, 6, v___y_682_);
lean_ctor_set(v___x_711_, 7, v___x_695_);
lean_ctor_set(v___x_711_, 8, v___x_690_);
lean_ctor_set(v___x_711_, 9, v___x_709_);
lean_ctor_set(v___x_711_, 10, v___y_682_);
lean_ctor_set(v___x_711_, 11, v___x_691_);
lean_ctor_set(v___x_711_, 12, v___x_710_);
lean_ctor_set(v___x_711_, 13, v___x_703_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*14, v_anyFailed_504_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*14 + 1, v_anyFailed_504_);
v_env_712_ = lean_ctor_get(v___x_704_, 0);
lean_inc_ref(v_env_712_);
lean_dec(v___x_704_);
v___x_713_ = l_Lean_diagnostics;
v___x_714_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__6(v___y_679_, v___x_713_);
v___x_715_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_712_);
lean_dec_ref(v_env_712_);
if (v___x_715_ == 0)
{
if (v___x_714_ == 0)
{
v___y_645_ = v___y_683_;
v___y_646_ = v___y_677_;
v___y_647_ = v___x_688_;
v___y_648_ = v___y_678_;
v___y_649_ = v___x_686_;
v___y_650_ = v___x_714_;
v___y_651_ = v___x_711_;
v___y_652_ = v___y_679_;
v___y_653_ = v___x_701_;
v___y_654_ = v___y_681_;
v___y_655_ = v___x_513_;
goto v___jp_644_;
}
else
{
v___y_645_ = v___y_683_;
v___y_646_ = v___y_677_;
v___y_647_ = v___x_688_;
v___y_648_ = v___y_678_;
v___y_649_ = v___x_686_;
v___y_650_ = v___x_714_;
v___y_651_ = v___x_711_;
v___y_652_ = v___y_679_;
v___y_653_ = v___x_701_;
v___y_654_ = v___y_681_;
v___y_655_ = v___x_715_;
goto v___jp_644_;
}
}
else
{
v___y_645_ = v___y_683_;
v___y_646_ = v___y_677_;
v___y_647_ = v___x_688_;
v___y_648_ = v___y_678_;
v___y_649_ = v___x_686_;
v___y_650_ = v___x_714_;
v___y_651_ = v___x_711_;
v___y_652_ = v___y_679_;
v___y_653_ = v___x_701_;
v___y_654_ = v___y_681_;
v___y_655_ = v___x_714_;
goto v___jp_644_;
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
v_a_716_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_687_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_687_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
v___jp_724_:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_array_get_size(v___y_731_);
v___x_733_ = lean_nat_dec_eq(v___x_732_, v___x_503_);
if (v___x_733_ == 0)
{
v___y_676_ = v___y_731_;
v___y_677_ = v___y_725_;
v___y_678_ = v___y_726_;
v___y_679_ = v___y_728_;
v___y_680_ = v___y_727_;
v___y_681_ = v___y_729_;
v___y_682_ = v___y_730_;
v___y_683_ = v_anyFailed_505_;
goto v___jp_675_;
}
else
{
v___y_676_ = v___y_731_;
v___y_677_ = v___y_725_;
v___y_678_ = v___y_726_;
v___y_679_ = v___y_728_;
v___y_680_ = v___y_727_;
v___y_681_ = v___y_729_;
v___y_682_ = v___y_730_;
v___y_683_ = v_anyFailed_504_;
goto v___jp_675_;
}
}
v___jp_734_:
{
lean_object* v___x_739_; lean_object* v_toEnvExtension_740_; lean_object* v_asyncMode_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_merged_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_756_; 
v___x_739_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_740_ = lean_ctor_get(v___x_739_, 0);
v_asyncMode_741_ = lean_ctor_get(v_toEnvExtension_740_, 2);
v___x_742_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_743_ = lean_box(0);
lean_inc_ref(v___y_737_);
v___x_744_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_742_, v___x_739_, v___y_737_, v_asyncMode_741_, v___x_743_);
v_merged_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v___x_744_, 1);
lean_dec(v_unused_757_);
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_merged_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_756_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_merged_745_);
lean_ctor_set(v___x_747_, 0, v___y_738_);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___y_738_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_merged_745_);
v___x_750_ = v_reuseFailAlloc_755_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l_Lean_Name_getRoot(v_a_517_);
v___x_752_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v___y_737_, v___x_751_);
if (v___y_735_ == 0)
{
v___y_725_ = v___y_735_;
v___y_726_ = v___x_751_;
v___y_727_ = v___y_737_;
v___y_728_ = v___y_736_;
v___y_729_ = v___x_750_;
v___y_730_ = v___x_743_;
v___y_731_ = v___x_752_;
goto v___jp_724_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_array_get_size(v___x_752_);
v___x_754_ = l_Array_filterMapM___at___00Lake_BuiltinLint_run_spec__9(v___x_750_, v___x_752_, v___x_503_, v___x_753_);
lean_dec_ref(v___x_752_);
v___y_725_ = v___y_735_;
v___y_726_ = v___x_751_;
v___y_727_ = v___y_737_;
v___y_728_ = v___y_736_;
v___y_729_ = v___x_750_;
v___y_730_ = v___x_743_;
v___y_731_ = v___x_754_;
goto v___jp_724_;
}
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref_known(v_envLinterModule_512_, 1);
v_a_825_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_516_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_516_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
v___jp_484_:
{
size_t v___x_486_; size_t v___x_487_; 
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_481_, v___x_486_);
v_i_481_ = v___x_487_;
v_b_482_ = v_a_485_;
goto _start;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = l_Lean_MessageData_toString(v_msg_490_);
v___x_492_ = lean_mk_io_user_error(v___x_491_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
v___jp_494_:
{
if (lean_obj_tag(v_a_495_) == 0)
{
lean_object* v_msg_496_; 
v_msg_496_ = lean_ctor_get(v_a_495_, 1);
lean_inc_ref(v_msg_496_);
lean_dec_ref_known(v_a_495_, 2);
v_msg_490_ = v_msg_496_;
goto v___jp_489_;
}
else
{
lean_object* v_id_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_id_497_ = lean_ctor_get(v_a_495_, 0);
lean_inc(v_id_497_);
lean_dec_ref_known(v_a_495_, 2);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___closed__0));
v___x_499_ = l_Nat_reprFast(v_id_497_);
v___x_500_ = lean_string_append(v___x_498_, v___x_499_);
lean_dec_ref(v___x_499_);
v___x_501_ = lean_mk_io_user_error(v___x_500_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
v___jp_506_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_st_ref_get(v___y_508_);
lean_dec(v___y_508_);
lean_dec(v___x_510_);
if (v___y_507_ == 0)
{
if (v_a_509_ == 0)
{
v_a_485_ = v_b_482_;
goto v___jp_484_;
}
else
{
v_a_485_ = v_anyFailed_505_;
goto v___jp_484_;
}
}
else
{
v_a_485_ = v_anyFailed_505_;
goto v___jp_484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11___boxed(lean_object* v___x_833_, lean_object* v_args_834_, lean_object* v_as_835_, lean_object* v_sz_836_, lean_object* v_i_837_, lean_object* v_b_838_, lean_object* v___y_839_){
_start:
{
size_t v_sz_boxed_840_; size_t v_i_boxed_841_; uint8_t v_b_boxed_842_; lean_object* v_res_843_; 
v_sz_boxed_840_ = lean_unbox_usize(v_sz_836_);
lean_dec(v_sz_836_);
v_i_boxed_841_ = lean_unbox_usize(v_i_837_);
lean_dec(v_i_837_);
v_b_boxed_842_ = lean_unbox(v_b_838_);
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___x_833_, v_args_834_, v_as_835_, v_sz_boxed_840_, v_i_boxed_841_, v_b_boxed_842_);
lean_dec_ref(v_as_835_);
lean_dec_ref(v_args_834_);
lean_dec(v___x_833_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__12_spec__13(lean_object* v_s_844_){
_start:
{
lean_object* v___x_846_; lean_object* v_putStr_847_; lean_object* v___x_848_; 
v___x_846_ = lean_get_stderr();
v_putStr_847_ = lean_ctor_get(v___x_846_, 4);
lean_inc_ref(v_putStr_847_);
lean_dec_ref(v___x_846_);
v___x_848_ = lean_apply_2(v_putStr_847_, v_s_844_, lean_box(0));
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__12_spec__13___boxed(lean_object* v_s_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__12_spec__13(v_s_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__12(lean_object* v_s_852_){
_start:
{
uint32_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = 10;
v___x_855_ = lean_string_push(v_s_852_, v___x_854_);
v___x_856_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__12_spec__13(v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__12___boxed(lean_object* v_s_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__12(v_s_857_);
return v_res_859_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_861_; lean_object* v___x_862_; 
v___x_861_ = 0;
v___x_862_ = lean_box_uint32(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_863_; lean_object* v___x_864_; 
v___x_863_ = 1;
v___x_864_ = lean_box_uint32(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_865_){
_start:
{
lean_object* v_mods_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v_anyFailed_870_; 
v_mods_867_ = lean_ctor_get(v_args_865_, 1);
v___x_868_ = lean_array_get_size(v_mods_867_);
v___x_869_ = lean_unsigned_to_nat(0u);
v_anyFailed_870_ = lean_nat_dec_eq(v___x_868_, v___x_869_);
if (v_anyFailed_870_ == 0)
{
size_t v_sz_871_; size_t v___x_872_; lean_object* v___x_873_; 
v_sz_871_ = lean_array_size(v_mods_867_);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__11(v___x_868_, v_args_865_, v_mods_867_, v_sz_871_, v___x_872_, v_anyFailed_870_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_887_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_887_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_887_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_887_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___x_878_; 
v___x_878_ = lean_unbox(v_a_874_);
lean_dec(v_a_874_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_879_);
v___x_881_ = v___x_876_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_883_);
v___x_885_ = v___x_876_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_873_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_873_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_897_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__12(v___x_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_897_, 0);
lean_dec(v_unused_906_);
v___x_899_ = v___x_897_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_dec(v___x_897_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_907_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_897_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_897_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lake_BuiltinLint_run(v_args_915_);
lean_dec_ref(v_args_915_);
return v_res_917_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_BuiltinLint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Linter_EnvLinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_BuiltinLint_run___boxed__const__1 = _init_l_Lake_BuiltinLint_run___boxed__const__1();
lean_mark_persistent(l_Lake_BuiltinLint_run___boxed__const__1);
l_Lake_BuiltinLint_run___boxed__const__2 = _init_l_Lake_BuiltinLint_run___boxed__const__2();
lean_mark_persistent(l_Lake_BuiltinLint_run___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_BuiltinLint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_EnvLinter(uint8_t builtin);
lean_object* initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_BuiltinLint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_EnvLinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_BuiltinLint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_BuiltinLint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_BuiltinLint(builtin);
}
#ifdef __cplusplus
}
#endif
