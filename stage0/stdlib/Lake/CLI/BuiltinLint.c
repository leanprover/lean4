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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Linter_EnvLinter_getChecks(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_findOLean(lean_object*);
lean_object* l_Lean_readModuleData(lean_object*);
lean_object* lean_compacted_region_free(size_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
lean_object* lean_get_stderr();
lean_object* lean_array_to_list(lean_object*);
static const lean_string_object l_Lake_BuiltinLint_leanOptOverrides___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__0_value;
static const lean_string_object l_Lake_BuiltinLint_leanOptOverrides___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__1 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__1_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__2_value_aux_0),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__1_value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__2 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__2_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__3 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__3_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__2_value),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__3_value)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__4 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__4_value;
static const lean_string_object l_Lake_BuiltinLint_leanOptOverrides___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__5 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__5_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__6_value_aux_0),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__5_value),LEAN_SCALAR_PTR_LITERAL(242, 180, 119, 173, 178, 109, 102, 175)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__6 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__6_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__6_value),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__3_value)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__7 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__7_value;
static const lean_array_object l_Lake_BuiltinLint_leanOptOverrides___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__4_value),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__7_value)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__8 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__8_value;
static lean_once_cell_t l_Lake_BuiltinLint_leanOptOverrides___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__9;
static const lean_array_object l_Lake_BuiltinLint_leanOptOverrides___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__4_value)}};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__10 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__10_value;
static lean_once_cell_t l_Lake_BuiltinLint_leanOptOverrides___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__11;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(size_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "-- Text linter diagnostics in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-- Linting passed for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "-- No environment linters registered for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__16_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_BuiltinLint_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "lake lint: no modules specified for builtin linting"};
static const lean_object* l_Lake_BuiltinLint_run___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_run___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_BuiltinLint_leanOptOverrides___closed__9(void){
_start:
{
lean_object* v_enableAll_24_; lean_object* v___x_25_; 
v_enableAll_24_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__8));
v___x_25_ = l_Lean_LeanOptions_ofArray(v_enableAll_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_leanOptOverrides___closed__11(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__10));
v___x_31_ = l_Lean_LeanOptions_ofArray(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides(lean_object* v_args_32_){
_start:
{
uint8_t v_scope_33_; lean_object* v_only_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v_scope_33_ = lean_ctor_get_uint8(v_args_32_, sizeof(void*)*2);
v_only_34_ = lean_ctor_get(v_args_32_, 0);
v___x_35_ = lean_array_get_size(v_only_34_);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_dec_eq(v___x_35_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Lake_BuiltinLint_leanOptOverrides___closed__9, &l_Lake_BuiltinLint_leanOptOverrides___closed__9_once, _init_l_Lake_BuiltinLint_leanOptOverrides___closed__9);
return v___x_38_;
}
else
{
switch(v_scope_33_)
{
case 0:
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(1);
return v___x_39_;
}
case 1:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Lake_BuiltinLint_leanOptOverrides___closed__11, &l_Lake_BuiltinLint_leanOptOverrides___closed__11_once, _init_l_Lake_BuiltinLint_leanOptOverrides___closed__11);
return v___x_40_;
}
default: 
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&l_Lake_BuiltinLint_leanOptOverrides___closed__9, &l_Lake_BuiltinLint_leanOptOverrides___closed__9_once, _init_l_Lake_BuiltinLint_leanOptOverrides___closed__9);
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_leanOptOverrides___boxed(lean_object* v_args_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lake_BuiltinLint_leanOptOverrides(v_args_42_);
lean_dec_ref(v_args_42_);
return v_res_43_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(lean_object* v___x_44_, lean_object* v_as_45_, size_t v_i_46_, size_t v_stop_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_usize_dec_eq(v_i_46_, v_stop_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_array_uget_borrowed(v_as_45_, v_i_46_);
v___x_50_ = l_Lean_Name_isSuffixOf(v___x_49_, v___x_44_);
if (v___x_50_ == 0)
{
size_t v___x_51_; size_t v___x_52_; 
v___x_51_ = ((size_t)1ULL);
v___x_52_ = lean_usize_add(v_i_46_, v___x_51_);
v_i_46_ = v___x_52_;
goto _start;
}
else
{
return v___x_50_;
}
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0___boxed(lean_object* v___x_55_, lean_object* v_as_56_, lean_object* v_i_57_, lean_object* v_stop_58_){
_start:
{
size_t v_i_boxed_59_; size_t v_stop_boxed_60_; uint8_t v_res_61_; lean_object* v_r_62_; 
v_i_boxed_59_ = lean_unbox_usize(v_i_57_);
lean_dec(v_i_57_);
v_stop_boxed_60_ = lean_unbox_usize(v_stop_58_);
lean_dec(v_stop_58_);
v_res_61_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v___x_55_, v_as_56_, v_i_boxed_59_, v_stop_boxed_60_);
lean_dec_ref(v_as_56_);
lean_dec(v___x_55_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(lean_object* v_args_63_, lean_object* v_as_64_, size_t v_i_65_, size_t v_stop_66_, lean_object* v_b_67_){
_start:
{
lean_object* v___y_69_; uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_eq(v_i_65_, v_stop_66_);
if (v___x_73_ == 0)
{
uint8_t v_scope_74_; lean_object* v_only_75_; lean_object* v___x_76_; uint8_t v___y_78_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_scope_74_ = lean_ctor_get_uint8(v_args_63_, sizeof(void*)*2);
v_only_75_ = lean_ctor_get(v_args_63_, 0);
v___x_76_ = lean_array_uget_borrowed(v_as_64_, v_i_65_);
v___x_88_ = lean_array_get_size(v_only_75_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_nat_dec_eq(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = lean_nat_dec_lt(v___x_89_, v___x_88_);
if (v___x_91_ == 0)
{
v___y_78_ = v___x_90_;
goto v___jp_77_;
}
else
{
if (v___x_91_ == 0)
{
v___y_78_ = v___x_90_;
goto v___jp_77_;
}
else
{
lean_object* v_linter_92_; size_t v___x_93_; size_t v___x_94_; uint8_t v___x_95_; 
v_linter_92_ = lean_ctor_get(v___x_76_, 0);
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_88_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_linter_92_, v_only_75_, v___x_93_, v___x_94_);
v___y_78_ = v___x_95_;
goto v___jp_77_;
}
}
}
else
{
v___y_78_ = v___x_90_;
goto v___jp_77_;
}
v___jp_77_:
{
if (v___y_78_ == 0)
{
v___y_69_ = v_b_67_;
goto v___jp_68_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_79_ = lean_array_get_size(v_only_75_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_nat_dec_eq(v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
lean_inc(v___x_76_);
v___x_82_ = lean_array_push(v_b_67_, v___x_76_);
v___y_69_ = v___x_82_;
goto v___jp_68_;
}
else
{
if (v_scope_74_ == 0)
{
lean_object* v_linter_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_linter_83_ = lean_ctor_get(v___x_76_, 0);
v___x_84_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__2));
v___x_85_ = l_Lean_Name_isPrefixOf(v___x_84_, v_linter_83_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_inc(v___x_76_);
v___x_86_ = lean_array_push(v_b_67_, v___x_76_);
v___y_69_ = v___x_86_;
goto v___jp_68_;
}
else
{
v___y_69_ = v_b_67_;
goto v___jp_68_;
}
}
else
{
lean_object* v___x_87_; 
lean_inc(v___x_76_);
v___x_87_ = lean_array_push(v_b_67_, v___x_76_);
v___y_69_ = v___x_87_;
goto v___jp_68_;
}
}
}
}
}
else
{
return v_b_67_;
}
v___jp_68_:
{
size_t v___x_70_; size_t v___x_71_; 
v___x_70_ = ((size_t)1ULL);
v___x_71_ = lean_usize_add(v_i_65_, v___x_70_);
v_i_65_ = v___x_71_;
v_b_67_ = v___y_69_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1___boxed(lean_object* v_args_96_, lean_object* v_as_97_, lean_object* v_i_98_, lean_object* v_stop_99_, lean_object* v_b_100_){
_start:
{
size_t v_i_boxed_101_; size_t v_stop_boxed_102_; lean_object* v_res_103_; 
v_i_boxed_101_ = lean_unbox_usize(v_i_98_);
lean_dec(v_i_98_);
v_stop_boxed_102_ = lean_unbox_usize(v_stop_99_);
lean_dec(v_stop_99_);
v_res_103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_96_, v_as_97_, v_i_boxed_101_, v_stop_boxed_102_, v_b_100_);
lean_dec_ref(v_as_97_);
lean_dec_ref(v_args_96_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(lean_object* v_pkgRoot_106_, lean_object* v_args_107_, lean_object* v_as_108_, size_t v_i_109_, size_t v_stop_110_, lean_object* v_b_111_){
_start:
{
lean_object* v___y_113_; uint8_t v___x_117_; 
v___x_117_ = lean_usize_dec_eq(v_i_109_, v_stop_110_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_145_; 
v___x_118_ = lean_array_uget(v_as_108_, v_i_109_);
v_fst_119_ = lean_ctor_get(v___x_118_, 0);
v_snd_120_ = lean_ctor_get(v___x_118_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_145_ == 0)
{
v___x_122_ = v___x_118_;
v_isShared_123_ = v_isSharedCheck_145_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_snd_120_);
lean_inc(v_fst_119_);
lean_dec(v___x_118_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_145_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___y_125_; uint8_t v___x_133_; 
v___x_133_ = l_Lean_Name_isPrefixOf(v_pkgRoot_106_, v_fst_119_);
if (v___x_133_ == 0)
{
lean_del_object(v___x_122_);
lean_dec(v_snd_120_);
lean_dec(v_fst_119_);
v___y_113_ = v_b_111_;
goto v___jp_112_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_snd_120_);
v___x_136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___closed__0));
v___x_137_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_137_ == 0)
{
lean_dec(v_snd_120_);
v___y_125_ = v___x_136_;
goto v___jp_124_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_le(v___x_135_, v___x_135_);
if (v___x_138_ == 0)
{
if (v___x_137_ == 0)
{
lean_dec(v_snd_120_);
v___y_125_ = v___x_136_;
goto v___jp_124_;
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_135_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_107_, v_snd_120_, v___x_139_, v___x_140_, v___x_136_);
lean_dec(v_snd_120_);
v___y_125_ = v___x_141_;
goto v___jp_124_;
}
}
else
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_135_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_107_, v_snd_120_, v___x_142_, v___x_143_, v___x_136_);
lean_dec(v_snd_120_);
v___y_125_ = v___x_144_;
goto v___jp_124_;
}
}
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = lean_array_get_size(v___y_125_);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_nat_dec_eq(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_130_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___y_125_);
v___x_130_ = v___x_122_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fst_119_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___y_125_);
v___x_130_ = v_reuseFailAlloc_132_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; 
v___x_131_ = lean_array_push(v_b_111_, v___x_130_);
v___y_113_ = v___x_131_;
goto v___jp_112_;
}
}
else
{
lean_dec_ref(v___y_125_);
lean_del_object(v___x_122_);
lean_dec(v_fst_119_);
v___y_113_ = v_b_111_;
goto v___jp_112_;
}
}
}
}
else
{
return v_b_111_;
}
v___jp_112_:
{
size_t v___x_114_; size_t v___x_115_; 
v___x_114_ = ((size_t)1ULL);
v___x_115_ = lean_usize_add(v_i_109_, v___x_114_);
v_i_109_ = v___x_115_;
v_b_111_ = v___y_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___boxed(lean_object* v_pkgRoot_146_, lean_object* v_args_147_, lean_object* v_as_148_, lean_object* v_i_149_, lean_object* v_stop_150_, lean_object* v_b_151_){
_start:
{
size_t v_i_boxed_152_; size_t v_stop_boxed_153_; lean_object* v_res_154_; 
v_i_boxed_152_ = lean_unbox_usize(v_i_149_);
lean_dec(v_i_149_);
v_stop_boxed_153_ = lean_unbox_usize(v_stop_150_);
lean_dec(v_stop_150_);
v_res_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_146_, v_args_147_, v_as_148_, v_i_boxed_152_, v_stop_boxed_153_, v_b_151_);
lean_dec_ref(v_as_148_);
lean_dec_ref(v_args_147_);
lean_dec(v_pkgRoot_146_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_157_, lean_object* v_args_158_, lean_object* v_pkgRoot_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_162_ = l_Lean_Linter_getAllLints(v_env_157_);
v___x_163_ = lean_array_get_size(v___x_162_);
v___x_164_ = lean_nat_dec_lt(v___x_160_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec_ref(v___x_162_);
return v___x_161_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_le(v___x_163_, v___x_163_);
if (v___x_165_ == 0)
{
if (v___x_164_ == 0)
{
lean_dec_ref(v___x_162_);
return v___x_161_;
}
else
{
size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_163_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_159_, v_args_158_, v___x_162_, v___x_166_, v___x_167_, v___x_161_);
lean_dec_ref(v___x_162_);
return v___x_168_;
}
}
else
{
size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((size_t)0ULL);
v___x_170_ = lean_usize_of_nat(v___x_163_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_159_, v_args_158_, v___x_162_, v___x_169_, v___x_170_, v___x_161_);
lean_dec_ref(v___x_162_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_172_, lean_object* v_args_173_, lean_object* v_pkgRoot_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_172_, v_args_173_, v_pkgRoot_174_);
lean_dec(v_pkgRoot_174_);
lean_dec_ref(v_args_173_);
lean_dec_ref(v_env_172_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(lean_object* v_modData_176_){
_start:
{
uint8_t v_isModule_178_; 
v_isModule_178_ = lean_ctor_get_uint8(v_modData_176_, sizeof(void*)*5);
return v_isModule_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule___boxed(lean_object* v_modData_179_, lean_object* v_a_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_modData_179_);
lean_dec_ref(v_modData_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lean_enable_initializer_execution();
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(size_t v_region_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_compacted_region_free(v_region_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4___boxed(lean_object* v_region_190_, lean_object* v_a_191_){
_start:
{
size_t v_region_boxed_192_; lean_object* v_res_193_; 
v_region_boxed_192_ = lean_unbox_usize(v_region_190_);
lean_dec(v_region_190_);
v_res_193_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__4(v_region_boxed_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_s_194_){
_start:
{
lean_object* v___x_196_; lean_object* v_putStr_197_; lean_object* v___x_198_; 
v___x_196_ = lean_get_stdout();
v_putStr_197_ = lean_ctor_get(v___x_196_, 4);
lean_inc_ref(v_putStr_197_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_apply_2(v_putStr_197_, v_s_194_, lean_box(0));
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_s_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v_s_199_);
return v_res_201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4(lean_object* v_opts_202_, lean_object* v_opt_203_){
_start:
{
lean_object* v_name_204_; lean_object* v_defValue_205_; lean_object* v_map_206_; lean_object* v___x_207_; 
v_name_204_ = lean_ctor_get(v_opt_203_, 0);
v_defValue_205_ = lean_ctor_get(v_opt_203_, 1);
v_map_206_ = lean_ctor_get(v_opts_202_, 0);
v___x_207_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_206_, v_name_204_);
if (lean_obj_tag(v___x_207_) == 0)
{
uint8_t v___x_208_; 
v___x_208_ = lean_unbox(v_defValue_205_);
return v___x_208_;
}
else
{
lean_object* v_val_209_; 
v_val_209_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v___x_207_, 1);
if (lean_obj_tag(v_val_209_) == 1)
{
uint8_t v_v_210_; 
v_v_210_ = lean_ctor_get_uint8(v_val_209_, 0);
lean_dec_ref_known(v_val_209_, 0);
return v_v_210_;
}
else
{
uint8_t v___x_211_; 
lean_dec(v_val_209_);
v___x_211_ = lean_unbox(v_defValue_205_);
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v_opts_212_, lean_object* v_opt_213_){
_start:
{
uint8_t v_res_214_; lean_object* v_r_215_; 
v_res_214_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4(v_opts_212_, v_opt_213_);
lean_dec_ref(v_opt_213_);
lean_dec_ref(v_opts_212_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5(lean_object* v_opts_216_, lean_object* v_opt_217_){
_start:
{
lean_object* v_name_218_; lean_object* v_defValue_219_; lean_object* v_map_220_; lean_object* v___x_221_; 
v_name_218_ = lean_ctor_get(v_opt_217_, 0);
v_defValue_219_ = lean_ctor_get(v_opt_217_, 1);
v_map_220_ = lean_ctor_get(v_opts_216_, 0);
v___x_221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_220_, v_name_218_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_inc(v_defValue_219_);
return v_defValue_219_;
}
else
{
lean_object* v_val_222_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
if (lean_obj_tag(v_val_222_) == 3)
{
lean_object* v_v_223_; 
v_v_223_ = lean_ctor_get(v_val_222_, 0);
lean_inc(v_v_223_);
lean_dec_ref_known(v_val_222_, 1);
return v_v_223_;
}
else
{
lean_dec(v_val_222_);
lean_inc(v_defValue_219_);
return v_defValue_219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v_opts_224_, lean_object* v_opt_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5(v_opts_224_, v_opt_225_);
lean_dec_ref(v_opt_225_);
lean_dec_ref(v_opts_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8(lean_object* v_s_227_){
_start:
{
lean_object* v___x_229_; lean_object* v_putStr_230_; lean_object* v___x_231_; 
v___x_229_ = lean_get_stderr();
v_putStr_230_ = lean_ctor_get(v___x_229_, 4);
lean_inc_ref(v_putStr_230_);
lean_dec_ref(v___x_229_);
v___x_231_ = lean_apply_2(v_putStr_230_, v_s_227_, lean_box(0));
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8___boxed(lean_object* v_s_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8(v_s_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8(lean_object* v_s_235_){
_start:
{
uint32_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = 10;
v___x_238_ = lean_string_push(v_s_235_, v___x_237_);
v___x_239_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__8_spec__8(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8___boxed(lean_object* v_s_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8(v_s_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__1(lean_object* v_s_243_){
_start:
{
uint32_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = 10;
v___x_246_ = lean_string_push(v_s_243_, v___x_245_);
v___x_247_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v_s_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v_s_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(lean_object* v___x_251_, lean_object* v_as_252_, size_t v_sz_253_, size_t v_i_254_, lean_object* v_b_255_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_lt(v_i_254_, v_sz_253_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_b_255_);
return v___x_258_;
}
else
{
lean_object* v_a_259_; lean_object* v_message_260_; lean_object* v___x_261_; uint8_t v_anyFailed_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_a_259_ = lean_array_uget_borrowed(v_as_252_, v_i_254_);
v_message_260_ = lean_ctor_get(v_a_259_, 1);
v___x_261_ = lean_unsigned_to_nat(0u);
v_anyFailed_262_ = lean_nat_dec_eq(v___x_251_, v___x_261_);
lean_inc_ref(v_message_260_);
v___x_263_ = l_Lean_SerialMessage_toString(v_message_260_, v_anyFailed_262_);
v___x_264_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; size_t v___x_266_; size_t v___x_267_; 
lean_dec_ref_known(v___x_264_, 1);
v___x_265_ = lean_box(0);
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_add(v_i_254_, v___x_266_);
v_i_254_ = v___x_267_;
v_b_255_ = v___x_265_;
goto _start;
}
else
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v___x_269_, lean_object* v_as_270_, lean_object* v_sz_271_, lean_object* v_i_272_, lean_object* v_b_273_, lean_object* v___y_274_){
_start:
{
size_t v_sz_boxed_275_; size_t v_i_boxed_276_; lean_object* v_res_277_; 
v_sz_boxed_275_ = lean_unbox_usize(v_sz_271_);
lean_dec(v_sz_271_);
v_i_boxed_276_ = lean_unbox_usize(v_i_272_);
lean_dec(v_i_272_);
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_269_, v_as_270_, v_sz_boxed_275_, v_i_boxed_276_, v_b_273_);
lean_dec_ref(v_as_270_);
lean_dec(v___x_269_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(lean_object* v___x_280_, lean_object* v_as_281_, size_t v_sz_282_, size_t v_i_283_, lean_object* v_b_284_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = lean_usize_dec_lt(v_i_283_, v_sz_282_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_b_284_);
return v___x_287_;
}
else
{
lean_object* v_a_288_; lean_object* v_fst_289_; lean_object* v_snd_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_a_288_ = lean_array_uget_borrowed(v_as_281_, v_i_283_);
v_fst_289_ = lean_ctor_get(v_a_288_, 0);
v_snd_290_ = lean_ctor_get(v_a_288_, 1);
v___x_291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__0));
lean_inc(v_fst_289_);
v___x_292_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_289_, v___x_286_);
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___closed__1));
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
v___x_296_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v___x_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; size_t v_sz_298_; size_t v___x_299_; lean_object* v___x_300_; 
lean_dec_ref_known(v___x_296_, 1);
v___x_297_ = lean_box(0);
v_sz_298_ = lean_array_size(v_snd_290_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__2(v___x_280_, v_snd_290_, v_sz_298_, v___x_299_, v___x_297_);
if (lean_obj_tag(v___x_300_) == 0)
{
size_t v___x_301_; size_t v___x_302_; 
lean_dec_ref_known(v___x_300_, 1);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_add(v_i_283_, v___x_301_);
v_i_283_ = v___x_302_;
v_b_284_ = v___x_297_;
goto _start;
}
else
{
return v___x_300_;
}
}
else
{
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v___x_304_, lean_object* v_as_305_, lean_object* v_sz_306_, lean_object* v_i_307_, lean_object* v_b_308_, lean_object* v___y_309_){
_start:
{
size_t v_sz_boxed_310_; size_t v_i_boxed_311_; lean_object* v_res_312_; 
v_sz_boxed_310_ = lean_unbox_usize(v_sz_306_);
lean_dec(v_sz_306_);
v_i_boxed_311_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_304_, v_as_305_, v_sz_boxed_310_, v_i_boxed_311_, v_b_308_);
lean_dec_ref(v_as_305_);
lean_dec(v___x_304_);
return v_res_312_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6(lean_object* v___x_313_, lean_object* v_as_314_, size_t v_i_315_, size_t v_stop_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = lean_usize_dec_eq(v_i_315_, v_stop_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v_snd_319_; lean_object* v_size_320_; lean_object* v___x_321_; uint8_t v___x_322_; uint8_t v___x_323_; 
v___x_318_ = lean_array_uget_borrowed(v_as_314_, v_i_315_);
v_snd_319_ = lean_ctor_get(v___x_318_, 1);
v_size_320_ = lean_ctor_get(v_snd_319_, 0);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = 1;
v___x_323_ = lean_nat_dec_eq(v_size_320_, v___x_321_);
if (v___x_323_ == 0)
{
return v___x_322_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = lean_nat_dec_eq(v___x_313_, v___x_321_);
if (v___x_324_ == 0)
{
size_t v___x_325_; size_t v___x_326_; 
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_add(v_i_315_, v___x_325_);
v_i_315_ = v___x_326_;
goto _start;
}
else
{
return v___x_322_;
}
}
}
else
{
uint8_t v___x_328_; 
v___x_328_ = 0;
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v___x_329_, lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_stop_332_){
_start:
{
size_t v_i_boxed_333_; size_t v_stop_boxed_334_; uint8_t v_res_335_; lean_object* v_r_336_; 
v_i_boxed_333_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_stop_boxed_334_ = lean_unbox_usize(v_stop_332_);
lean_dec(v_stop_332_);
v_res_335_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6(v___x_329_, v_as_330_, v_i_boxed_333_, v_stop_boxed_334_);
lean_dec_ref(v_as_330_);
lean_dec(v___x_329_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(32u);
v___x_350_ = lean_mk_empty_array_with_capacity(v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10(void){
_start:
{
size_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_352_ = ((size_t)5ULL);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_unsigned_to_nat(32u);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_356_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__9);
v___x_357_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
lean_ctor_set(v___x_357_, 2, v___x_353_);
lean_ctor_set(v___x_357_, 3, v___x_353_);
lean_ctor_set_usize(v___x_357_, 4, v___x_352_);
return v___x_357_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11(void){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_358_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__11);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = l_Lean_NameSet_empty;
v___x_364_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10);
v___x_365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
lean_ctor_set(v___x_365_, 2, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = l_Lean_firstFrontendMacroScope;
v___x_368_ = lean_nat_add(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20(void){
_start:
{
lean_object* v___x_379_; uint64_t v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10);
v___x_380_ = 0ULL;
v___x_381_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set_uint64(v___x_381_, sizeof(void*)*1, v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v_anyFailed_384_; lean_object* v___x_385_; 
v___x_382_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__10);
v___x_383_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__12);
v_anyFailed_384_ = 1;
v___x_385_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
lean_ctor_set(v___x_385_, 2, v___x_382_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*3, v_anyFailed_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7(lean_object* v___x_391_, lean_object* v_args_392_, uint8_t v_scope_393_, lean_object* v___y_394_, uint8_t v___y_395_, lean_object* v_as_396_, size_t v_sz_397_, size_t v_i_398_, uint8_t v_b_399_){
_start:
{
uint8_t v_a_402_; lean_object* v_msg_407_; lean_object* v_a_412_; lean_object* v___x_420_; uint8_t v_anyFailed_421_; uint8_t v_anyFailed_422_; lean_object* v___y_424_; uint8_t v___y_425_; uint8_t v_a_426_; lean_object* v___y_429_; uint8_t v___y_430_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; uint8_t v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___x_455_; lean_object* v_envLinterModule_456_; uint8_t v___x_457_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v_anyFailed_421_ = lean_nat_dec_eq(v___x_391_, v___x_420_);
v_anyFailed_422_ = 1;
v___x_455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__4));
v_envLinterModule_456_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_456_, 0, v___x_455_);
lean_ctor_set_uint8(v_envLinterModule_456_, sizeof(void*)*1, v_anyFailed_421_);
lean_ctor_set_uint8(v_envLinterModule_456_, sizeof(void*)*1 + 1, v_anyFailed_422_);
lean_ctor_set_uint8(v_envLinterModule_456_, sizeof(void*)*1 + 2, v_anyFailed_421_);
v___x_457_ = lean_usize_dec_lt(v_i_398_, v_sz_397_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec_ref_known(v_envLinterModule_456_, 1);
v___x_458_ = lean_box(v_b_399_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___y_463_; uint8_t v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___y_470_; lean_object* v___y_492_; uint8_t v___y_493_; lean_object* v___y_494_; size_t v___y_495_; uint8_t v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_556_; lean_object* v___y_557_; uint8_t v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; size_t v___y_561_; uint8_t v___y_562_; lean_object* v___y_563_; uint8_t v___y_564_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; uint8_t v___y_589_; lean_object* v___x_630_; 
lean_dec_ref_known(v___x_460_, 1);
v_a_461_ = lean_array_uget_borrowed(v_as_396_, v_i_398_);
lean_inc(v_a_461_);
v___x_630_ = l_Lean_findOLean(v_a_461_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l_Lean_readModuleData(v_a_631_);
lean_dec(v_a_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v_fst_634_; lean_object* v_snd_635_; uint8_t v___x_636_; uint8_t v___y_638_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v_fst_634_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_fst_634_);
v_snd_635_ = lean_ctor_get(v_a_633_, 1);
lean_inc(v_snd_635_);
lean_dec(v_a_633_);
v___x_636_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_getIsModule(v_fst_634_);
lean_dec(v_fst_634_);
if (v___x_636_ == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 2;
v___y_638_ = v___x_672_;
goto v___jp_637_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = 0;
v___y_638_ = v___x_673_;
goto v___jp_637_;
}
v___jp_637_:
{
size_t v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_unbox_usize(v_snd_635_);
lean_dec(v_snd_635_);
v___x_640_ = lean_compacted_region_free(v___x_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint32_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref_known(v___x_640_, 1);
lean_inc(v_a_461_);
v___x_641_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_641_, 0, v_a_461_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v_anyFailed_421_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1 + 1, v_anyFailed_422_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1 + 2, v_anyFailed_421_);
v___x_642_ = lean_unsigned_to_nat(2u);
v___x_643_ = lean_mk_empty_array_with_capacity(v___x_642_);
v___x_644_ = lean_array_push(v___x_643_, v___x_641_);
v___x_645_ = lean_array_push(v___x_644_, v_envLinterModule_456_);
v___x_646_ = l_Lean_Options_empty;
v___x_647_ = 1024;
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__24));
v___x_649_ = lean_box(1);
v___x_650_ = l_Lean_importModules(v___x_645_, v___x_646_, v___x_647_, v___x_648_, v_anyFailed_421_, v_anyFailed_422_, v___y_638_, v___x_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = l_Lean_Name_getRoot(v_a_461_);
v___x_653_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_a_651_, v_args_392_, v___x_652_);
v___x_654_ = lean_array_get_size(v___x_653_);
v___x_655_ = lean_nat_dec_eq(v___x_654_, v___x_420_);
if (v___x_655_ == 0)
{
v___y_585_ = v___x_646_;
v___y_586_ = v___x_653_;
v___y_587_ = v_a_651_;
v___y_588_ = v___x_652_;
v___y_589_ = v_anyFailed_422_;
goto v___jp_584_;
}
else
{
v___y_585_ = v___x_646_;
v___y_586_ = v___x_653_;
v___y_587_ = v_a_651_;
v___y_588_ = v___x_652_;
v___y_589_ = v_anyFailed_421_;
goto v___jp_584_;
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_650_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_650_);
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
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec_ref_known(v_envLinterModule_456_, 1);
v_a_664_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_640_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_640_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref_known(v_envLinterModule_456_, 1);
v_a_674_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_632_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_632_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
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
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref_known(v_envLinterModule_456_, 1);
v_a_682_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_630_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_630_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
v___jp_462_:
{
if (v___y_470_ == 0)
{
lean_dec_ref(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
if (v___y_464_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__5));
lean_inc(v_a_461_);
v___x_472_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_461_, v_anyFailed_422_);
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
lean_dec_ref(v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v___x_476_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v___x_475_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_dec_ref_known(v___x_476_, 1);
v___y_424_ = v___y_463_;
v___y_425_ = v___y_464_;
v_a_426_ = v___y_470_;
goto v___jp_423_;
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
lean_dec(v___y_463_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_486_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_io_error_to_string(v_a_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set_tag(v___x_479_, 3);
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_485_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_MessageData_ofFormat(v___x_483_);
v_msg_407_ = v___x_484_;
goto v___jp_406_;
}
}
}
}
else
{
v___y_424_ = v___y_463_;
v___y_425_ = v___y_464_;
v_a_426_ = v___y_470_;
goto v___jp_423_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__7));
lean_inc(v_a_461_);
v___x_488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_461_, v___y_470_);
v___x_489_ = lean_string_append(v___x_487_, v___x_488_);
lean_dec_ref(v___x_488_);
if (v___y_395_ == 0)
{
uint8_t v___x_490_; 
v___x_490_ = 2;
v___y_429_ = v___y_463_;
v___y_430_ = v___y_464_;
v___y_431_ = v___y_466_;
v___y_432_ = v___y_465_;
v___y_433_ = v___y_467_;
v___y_434_ = v___y_468_;
v___y_435_ = v___y_470_;
v___y_436_ = v___x_489_;
v___y_437_ = v___y_469_;
v___y_438_ = v___x_490_;
goto v___jp_428_;
}
else
{
v___y_429_ = v___y_463_;
v___y_430_ = v___y_464_;
v___y_431_ = v___y_466_;
v___y_432_ = v___y_465_;
v___y_433_ = v___y_467_;
v___y_434_ = v___y_468_;
v___y_435_ = v___y_470_;
v___y_436_ = v___x_489_;
v___y_437_ = v___y_469_;
v___y_438_ = v_scope_393_;
goto v___jp_428_;
}
}
}
v___jp_491_:
{
lean_object* v_fileName_500_; lean_object* v_fileMap_501_; lean_object* v_currRecDepth_502_; lean_object* v_ref_503_; lean_object* v_currNamespace_504_; lean_object* v_openDecls_505_; lean_object* v_initHeartbeats_506_; lean_object* v_maxHeartbeats_507_; lean_object* v_quotContext_508_; lean_object* v_currMacroScope_509_; lean_object* v_cancelTk_x3f_510_; uint8_t v_suppressElabErrors_511_; lean_object* v_inheritedTraceOptions_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_552_; 
v_fileName_500_ = lean_ctor_get(v___y_498_, 0);
v_fileMap_501_ = lean_ctor_get(v___y_498_, 1);
v_currRecDepth_502_ = lean_ctor_get(v___y_498_, 3);
v_ref_503_ = lean_ctor_get(v___y_498_, 5);
v_currNamespace_504_ = lean_ctor_get(v___y_498_, 6);
v_openDecls_505_ = lean_ctor_get(v___y_498_, 7);
v_initHeartbeats_506_ = lean_ctor_get(v___y_498_, 8);
v_maxHeartbeats_507_ = lean_ctor_get(v___y_498_, 9);
v_quotContext_508_ = lean_ctor_get(v___y_498_, 10);
v_currMacroScope_509_ = lean_ctor_get(v___y_498_, 11);
v_cancelTk_x3f_510_ = lean_ctor_get(v___y_498_, 12);
v_suppressElabErrors_511_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_512_ = lean_ctor_get(v___y_498_, 13);
v_isSharedCheck_552_ = !lean_is_exclusive(v___y_498_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; lean_object* v_unused_554_; 
v_unused_553_ = lean_ctor_get(v___y_498_, 4);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v___y_498_, 2);
lean_dec(v_unused_554_);
v___x_514_ = v___y_498_;
v_isShared_515_ = v_isSharedCheck_552_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_inheritedTraceOptions_512_);
lean_inc(v_cancelTk_x3f_510_);
lean_inc(v_currMacroScope_509_);
lean_inc(v_quotContext_508_);
lean_inc(v_maxHeartbeats_507_);
lean_inc(v_initHeartbeats_506_);
lean_inc(v_openDecls_505_);
lean_inc(v_currNamespace_504_);
lean_inc(v_ref_503_);
lean_inc(v_currRecDepth_502_);
lean_inc(v_fileMap_501_);
lean_inc(v_fileName_500_);
lean_dec(v___y_498_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_552_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___y_497_, v___y_499_);
lean_dec(v___y_497_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = l_Lean_maxRecDepth;
v___x_519_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__5(v___y_494_, v___x_518_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 4, v___x_519_);
lean_ctor_set(v___x_514_, 2, v___y_494_);
v___x_521_ = v___x_514_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_fileName_500_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_fileMap_501_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v___y_494_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_currRecDepth_502_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v_ref_503_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_currNamespace_504_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_openDecls_505_);
lean_ctor_set(v_reuseFailAlloc_550_, 8, v_initHeartbeats_506_);
lean_ctor_set(v_reuseFailAlloc_550_, 9, v_maxHeartbeats_507_);
lean_ctor_set(v_reuseFailAlloc_550_, 10, v_quotContext_508_);
lean_ctor_set(v_reuseFailAlloc_550_, 11, v_currMacroScope_509_);
lean_ctor_set(v_reuseFailAlloc_550_, 12, v_cancelTk_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_550_, 13, v_inheritedTraceOptions_512_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*14 + 1, v_suppressElabErrors_511_);
v___x_521_ = v_reuseFailAlloc_550_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*14, v___y_496_);
v___x_522_ = l_Lean_Linter_EnvLinter_getChecks(v_scope_393_, v___y_394_, v___x_521_, v___y_499_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = lean_array_get_size(v_a_523_);
v___x_525_ = lean_nat_dec_eq(v___x_524_, v___x_420_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Linter_EnvLinter_lintCore(v_a_517_, v_a_523_, v___x_521_, v___y_499_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = lean_array_get_size(v_a_527_);
v___x_529_ = lean_nat_dec_lt(v___x_420_, v___x_528_);
if (v___x_529_ == 0)
{
v___y_463_ = v___y_492_;
v___y_464_ = v___y_493_;
v___y_465_ = v___x_524_;
v___y_466_ = v___y_499_;
v___y_467_ = v_a_517_;
v___y_468_ = v___x_521_;
v___y_469_ = v_a_527_;
v___y_470_ = v___x_525_;
goto v___jp_462_;
}
else
{
if (v___x_529_ == 0)
{
v___y_463_ = v___y_492_;
v___y_464_ = v___y_493_;
v___y_465_ = v___x_524_;
v___y_466_ = v___y_499_;
v___y_467_ = v_a_517_;
v___y_468_ = v___x_521_;
v___y_469_ = v_a_527_;
v___y_470_ = v___x_525_;
goto v___jp_462_;
}
else
{
size_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_usize_of_nat(v___x_528_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__6(v___x_524_, v_a_527_, v___y_495_, v___x_530_);
v___y_463_ = v___y_492_;
v___y_464_ = v___y_493_;
v___y_465_ = v___x_524_;
v___y_466_ = v___y_499_;
v___y_467_ = v_a_517_;
v___y_468_ = v___x_521_;
v___y_469_ = v_a_527_;
v___y_470_ = v___x_531_;
goto v___jp_462_;
}
}
}
else
{
lean_object* v_a_532_; 
lean_dec_ref(v___x_521_);
lean_dec(v_a_517_);
lean_dec(v___y_499_);
lean_dec(v___y_492_);
v_a_532_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_526_, 1);
v_a_412_ = v_a_532_;
goto v___jp_411_;
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_a_523_);
lean_dec_ref(v___x_521_);
lean_dec(v_a_517_);
lean_dec(v___y_499_);
v___x_533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__8));
lean_inc(v_a_461_);
v___x_534_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_461_, v___x_525_);
v___x_535_ = lean_string_append(v___x_533_, v___x_534_);
lean_dec_ref(v___x_534_);
v___x_536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__6));
v___x_537_ = lean_string_append(v___x_535_, v___x_536_);
v___x_538_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__1(v___x_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_dec_ref_known(v___x_538_, 1);
v___y_424_ = v___y_492_;
v___y_425_ = v___y_493_;
v_a_426_ = v_anyFailed_421_;
goto v___jp_423_;
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
lean_dec(v___y_492_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_io_error_to_string(v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 3);
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_MessageData_ofFormat(v___x_545_);
v_msg_407_ = v___x_546_;
goto v___jp_406_;
}
}
}
}
}
else
{
lean_object* v_a_549_; 
lean_dec_ref(v___x_521_);
lean_dec(v_a_517_);
lean_dec(v___y_499_);
lean_dec(v___y_492_);
v_a_549_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_522_, 1);
v_a_412_ = v_a_549_;
goto v___jp_411_;
}
}
}
else
{
lean_object* v_a_551_; 
lean_del_object(v___x_514_);
lean_dec_ref(v_inheritedTraceOptions_512_);
lean_dec(v_cancelTk_x3f_510_);
lean_dec(v_currMacroScope_509_);
lean_dec(v_quotContext_508_);
lean_dec(v_maxHeartbeats_507_);
lean_dec(v_initHeartbeats_506_);
lean_dec(v_openDecls_505_);
lean_dec(v_currNamespace_504_);
lean_dec(v_ref_503_);
lean_dec(v_currRecDepth_502_);
lean_dec_ref(v_fileMap_501_);
lean_dec_ref(v_fileName_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_492_);
v_a_551_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_516_, 1);
v_a_412_ = v_a_551_;
goto v___jp_411_;
}
}
}
v___jp_555_:
{
if (v___y_564_ == 0)
{
lean_object* v___x_565_; lean_object* v_env_566_; lean_object* v_nextMacroScope_567_; lean_object* v_ngen_568_; lean_object* v_auxDeclNGen_569_; lean_object* v_traceState_570_; lean_object* v_messages_571_; lean_object* v_infoState_572_; lean_object* v_snapshotTasks_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
v___x_565_ = lean_st_ref_take(v___y_556_);
v_env_566_ = lean_ctor_get(v___x_565_, 0);
v_nextMacroScope_567_ = lean_ctor_get(v___x_565_, 1);
v_ngen_568_ = lean_ctor_get(v___x_565_, 2);
v_auxDeclNGen_569_ = lean_ctor_get(v___x_565_, 3);
v_traceState_570_ = lean_ctor_get(v___x_565_, 4);
v_messages_571_ = lean_ctor_get(v___x_565_, 6);
v_infoState_572_ = lean_ctor_get(v___x_565_, 7);
v_snapshotTasks_573_ = lean_ctor_get(v___x_565_, 8);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_582_ == 0)
{
lean_object* v_unused_583_; 
v_unused_583_ = lean_ctor_get(v___x_565_, 5);
lean_dec(v_unused_583_);
v___x_575_ = v___x_565_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_snapshotTasks_573_);
lean_inc(v_infoState_572_);
lean_inc(v_messages_571_);
lean_inc(v_traceState_570_);
lean_inc(v_auxDeclNGen_569_);
lean_inc(v_ngen_568_);
lean_inc(v_nextMacroScope_567_);
lean_inc(v_env_566_);
lean_dec(v___x_565_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = l_Lean_Kernel_enableDiag(v_env_566_, v___y_562_);
lean_inc_ref(v___y_560_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 5, v___y_560_);
lean_ctor_set(v___x_575_, 0, v___x_577_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_nextMacroScope_567_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_ngen_568_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_auxDeclNGen_569_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_traceState_570_);
lean_ctor_set(v_reuseFailAlloc_581_, 5, v___y_560_);
lean_ctor_set(v_reuseFailAlloc_581_, 6, v_messages_571_);
lean_ctor_set(v_reuseFailAlloc_581_, 7, v_infoState_572_);
lean_ctor_set(v_reuseFailAlloc_581_, 8, v_snapshotTasks_573_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = lean_st_ref_set(v___y_556_, v___x_579_);
lean_inc(v___y_556_);
v___y_492_ = v___y_556_;
v___y_493_ = v___y_558_;
v___y_494_ = v___y_557_;
v___y_495_ = v___y_561_;
v___y_496_ = v___y_562_;
v___y_497_ = v___y_563_;
v___y_498_ = v___y_559_;
v___y_499_ = v___y_556_;
goto v___jp_491_;
}
}
}
else
{
lean_inc(v___y_556_);
v___y_492_ = v___y_556_;
v___y_493_ = v___y_558_;
v___y_494_ = v___y_557_;
v___y_495_ = v___y_561_;
v___y_496_ = v___y_562_;
v___y_497_ = v___y_563_;
v___y_498_ = v___y_559_;
v___y_499_ = v___y_556_;
goto v___jp_491_;
}
}
v___jp_584_:
{
lean_object* v___x_590_; size_t v_sz_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_590_ = lean_box(0);
v_sz_591_ = lean_array_size(v___y_586_);
v___x_592_ = ((size_t)0ULL);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__3(v___x_391_, v___y_586_, v_sz_591_, v___x_592_, v___x_590_);
lean_dec_ref(v___y_586_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_env_618_; lean_object* v___x_619_; uint8_t v___x_620_; uint8_t v___x_621_; 
lean_dec_ref_known(v___x_593_, 1);
v___x_594_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__13);
v___x_595_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__14);
v___x_596_ = lean_io_get_num_heartbeats();
v___x_597_ = l_Lean_firstFrontendMacroScope;
v___x_598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__15);
v___x_599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__18));
v___x_600_ = lean_box(0);
v___x_601_ = lean_box(0);
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__19));
v___x_603_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__20);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__21);
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__22));
v___x_606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_606_, 0, v___y_587_);
lean_ctor_set(v___x_606_, 1, v___x_598_);
lean_ctor_set(v___x_606_, 2, v___x_599_);
lean_ctor_set(v___x_606_, 3, v___x_602_);
lean_ctor_set(v___x_606_, 4, v___x_603_);
lean_ctor_set(v___x_606_, 5, v___x_594_);
lean_ctor_set(v___x_606_, 6, v___x_595_);
lean_ctor_set(v___x_606_, 7, v___x_604_);
lean_ctor_set(v___x_606_, 8, v___x_605_);
v___x_607_ = lean_st_mk_ref(v___x_606_);
v___x_608_ = l_Lean_inheritedTraceOptions;
v___x_609_ = lean_st_ref_get(v___x_608_);
v___x_610_ = lean_st_ref_get(v___x_607_);
v___x_611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__23));
v___x_612_ = l_Lean_instInhabitedFileMap_default;
v___x_613_ = lean_unsigned_to_nat(1000u);
v___x_614_ = lean_box(0);
v___x_615_ = l_Lean_Core_getMaxHeartbeats(v___y_585_);
v___x_616_ = lean_box(0);
lean_inc_ref(v___y_585_);
v___x_617_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_617_, 0, v___x_611_);
lean_ctor_set(v___x_617_, 1, v___x_612_);
lean_ctor_set(v___x_617_, 2, v___y_585_);
lean_ctor_set(v___x_617_, 3, v___x_420_);
lean_ctor_set(v___x_617_, 4, v___x_613_);
lean_ctor_set(v___x_617_, 5, v___x_614_);
lean_ctor_set(v___x_617_, 6, v___x_600_);
lean_ctor_set(v___x_617_, 7, v___x_601_);
lean_ctor_set(v___x_617_, 8, v___x_596_);
lean_ctor_set(v___x_617_, 9, v___x_615_);
lean_ctor_set(v___x_617_, 10, v___x_600_);
lean_ctor_set(v___x_617_, 11, v___x_597_);
lean_ctor_set(v___x_617_, 12, v___x_616_);
lean_ctor_set(v___x_617_, 13, v___x_609_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*14, v_anyFailed_421_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*14 + 1, v_anyFailed_421_);
v_env_618_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_618_);
lean_dec(v___x_610_);
v___x_619_ = l_Lean_diagnostics;
v___x_620_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__4(v___y_585_, v___x_619_);
v___x_621_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_618_);
lean_dec_ref(v_env_618_);
if (v___x_621_ == 0)
{
if (v___x_620_ == 0)
{
v___y_556_ = v___x_607_;
v___y_557_ = v___y_585_;
v___y_558_ = v___y_589_;
v___y_559_ = v___x_617_;
v___y_560_ = v___x_594_;
v___y_561_ = v___x_592_;
v___y_562_ = v___x_620_;
v___y_563_ = v___y_588_;
v___y_564_ = v___x_457_;
goto v___jp_555_;
}
else
{
v___y_556_ = v___x_607_;
v___y_557_ = v___y_585_;
v___y_558_ = v___y_589_;
v___y_559_ = v___x_617_;
v___y_560_ = v___x_594_;
v___y_561_ = v___x_592_;
v___y_562_ = v___x_620_;
v___y_563_ = v___y_588_;
v___y_564_ = v___x_621_;
goto v___jp_555_;
}
}
else
{
v___y_556_ = v___x_607_;
v___y_557_ = v___y_585_;
v___y_558_ = v___y_589_;
v___y_559_ = v___x_617_;
v___y_560_ = v___x_594_;
v___y_561_ = v___x_592_;
v___y_562_ = v___x_620_;
v___y_563_ = v___y_588_;
v___y_564_ = v___x_620_;
goto v___jp_555_;
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec_ref(v___y_585_);
v_a_622_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_593_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_593_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref_known(v_envLinterModule_456_, 1);
v_a_690_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_460_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_460_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
v___jp_401_:
{
size_t v___x_403_; size_t v___x_404_; 
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_398_, v___x_403_);
v_i_398_ = v___x_404_;
v_b_399_ = v_a_402_;
goto _start;
}
v___jp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = l_Lean_MessageData_toString(v_msg_407_);
v___x_409_ = lean_mk_io_user_error(v___x_408_);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
v___jp_411_:
{
if (lean_obj_tag(v_a_412_) == 0)
{
lean_object* v_msg_413_; 
v_msg_413_ = lean_ctor_get(v_a_412_, 1);
lean_inc_ref(v_msg_413_);
lean_dec_ref_known(v_a_412_, 2);
v_msg_407_ = v_msg_413_;
goto v___jp_406_;
}
else
{
lean_object* v_id_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_id_414_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_id_414_);
lean_dec_ref_known(v_a_412_, 2);
v___x_415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___closed__0));
v___x_416_ = l_Nat_reprFast(v_id_414_);
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
lean_dec_ref(v___x_416_);
v___x_418_ = lean_mk_io_user_error(v___x_417_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
v___jp_423_:
{
lean_object* v___x_427_; 
v___x_427_ = lean_st_ref_get(v___y_424_);
lean_dec(v___y_424_);
lean_dec(v___x_427_);
if (v___y_425_ == 0)
{
if (v_a_426_ == 0)
{
v_a_402_ = v_b_399_;
goto v___jp_401_;
}
else
{
v_a_402_ = v_anyFailed_422_;
goto v___jp_401_;
}
}
else
{
v_a_402_ = v_anyFailed_422_;
goto v___jp_401_;
}
}
v___jp_428_:
{
uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_439_ = 1;
v___x_440_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_437_, v___y_433_, v_anyFailed_422_, v___y_436_, v___y_438_, v___x_439_, v___y_432_, v_anyFailed_422_, v___y_434_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_434_);
lean_dec_ref(v___y_433_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = l_Lean_MessageData_toString(v_a_441_);
v___x_443_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__0(v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_dec_ref_known(v___x_443_, 1);
v___y_424_ = v___y_429_;
v___y_425_ = v___y_430_;
v_a_426_ = v___y_435_;
goto v___jp_423_;
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_453_; 
lean_dec(v___y_429_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_453_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_453_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = lean_io_error_to_string(v_a_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 3);
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_MessageData_ofFormat(v___x_450_);
v_msg_407_ = v___x_451_;
goto v___jp_406_;
}
}
}
}
else
{
lean_object* v_a_454_; 
lean_dec(v___y_429_);
v_a_454_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_440_, 1);
v_a_412_ = v_a_454_;
goto v___jp_411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object* v___x_698_, lean_object* v_args_699_, lean_object* v_scope_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v_as_703_, lean_object* v_sz_704_, lean_object* v_i_705_, lean_object* v_b_706_, lean_object* v___y_707_){
_start:
{
uint8_t v_scope_boxed_708_; uint8_t v___y_11198__boxed_709_; size_t v_sz_boxed_710_; size_t v_i_boxed_711_; uint8_t v_b_boxed_712_; lean_object* v_res_713_; 
v_scope_boxed_708_ = lean_unbox(v_scope_700_);
v___y_11198__boxed_709_ = lean_unbox(v___y_702_);
v_sz_boxed_710_ = lean_unbox_usize(v_sz_704_);
lean_dec(v_sz_704_);
v_i_boxed_711_ = lean_unbox_usize(v_i_705_);
lean_dec(v_i_705_);
v_b_boxed_712_ = lean_unbox(v_b_706_);
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7(v___x_698_, v_args_699_, v_scope_boxed_708_, v___y_701_, v___y_11198__boxed_709_, v_as_703_, v_sz_boxed_710_, v_i_boxed_711_, v_b_boxed_712_);
lean_dec_ref(v_as_703_);
lean_dec(v___y_701_);
lean_dec_ref(v_args_699_);
lean_dec(v___x_698_);
return v_res_713_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_715_; lean_object* v___x_716_; 
v___x_715_ = 0;
v___x_716_ = lean_box_uint32(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_717_; lean_object* v___x_718_; 
v___x_717_ = 1;
v___x_718_ = lean_box_uint32(v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_719_){
_start:
{
uint8_t v_scope_721_; lean_object* v_only_722_; lean_object* v_mods_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v_anyFailed_726_; 
v_scope_721_ = lean_ctor_get_uint8(v_args_719_, sizeof(void*)*2);
v_only_722_ = lean_ctor_get(v_args_719_, 0);
v_mods_723_ = lean_ctor_get(v_args_719_, 1);
lean_inc_ref(v_mods_723_);
v___x_724_ = lean_array_get_size(v_mods_723_);
v___x_725_ = lean_unsigned_to_nat(0u);
v_anyFailed_726_ = lean_nat_dec_eq(v___x_724_, v___x_725_);
if (v_anyFailed_726_ == 0)
{
lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___y_730_; 
v___x_727_ = lean_array_get_size(v_only_722_);
v___x_728_ = lean_nat_dec_eq(v___x_727_, v___x_725_);
if (v___x_728_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
lean_inc_ref(v_only_722_);
v___x_756_ = lean_array_to_list(v_only_722_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___y_730_ = v___x_757_;
goto v___jp_729_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = lean_box(0);
v___y_730_ = v___x_758_;
goto v___jp_729_;
}
v___jp_729_:
{
size_t v_sz_731_; size_t v___x_732_; lean_object* v___x_733_; 
v_sz_731_ = lean_array_size(v_mods_723_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__7(v___x_724_, v_args_719_, v_scope_721_, v___y_730_, v___x_728_, v_mods_723_, v_sz_731_, v___x_732_, v_anyFailed_726_);
lean_dec_ref(v_mods_723_);
lean_dec(v___y_730_);
lean_dec_ref(v_args_719_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_747_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_747_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_747_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_747_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___x_738_; 
v___x_738_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_739_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_743_);
v___x_745_ = v___x_736_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_a_748_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_733_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_733_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec_ref(v_mods_723_);
lean_dec_ref(v_args_719_);
v___x_759_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_760_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__8(v___x_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_768_; 
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v___x_760_, 0);
lean_dec(v_unused_769_);
v___x_762_ = v___x_760_;
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
else
{
lean_dec(v___x_760_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_768_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_760_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_760_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lake_BuiltinLint_run(v_args_778_);
return v_res_780_;
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
