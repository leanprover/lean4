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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* lean_get_stdout();
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_enable_initializer_execution();
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Linter_getAllLints(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_SerialMessage_toString(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0 = (const lean_object*)&l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-- Linting passed for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__7_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "-- No environment linters registered for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__18_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__18_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__19_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__21_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__24_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "-- Text linter diagnostics in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__27_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__28_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(lean_object* v_pkgRoot_104_, lean_object* v_args_105_, lean_object* v_as_106_, size_t v_i_107_, size_t v_stop_108_, lean_object* v_b_109_){
_start:
{
lean_object* v___y_111_; uint8_t v___x_115_; 
v___x_115_ = lean_usize_dec_eq(v_i_107_, v_stop_108_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v_fst_117_; lean_object* v_snd_118_; uint8_t v___x_119_; 
v___x_116_ = lean_array_uget_borrowed(v_as_106_, v_i_107_);
v_fst_117_ = lean_ctor_get(v___x_116_, 0);
v_snd_118_ = lean_ctor_get(v___x_116_, 1);
v___x_119_ = l_Lean_Name_isPrefixOf(v_pkgRoot_104_, v_fst_117_);
if (v___x_119_ == 0)
{
v___y_111_ = v_b_109_;
goto v___jp_110_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_get_size(v_snd_118_);
v___x_122_ = lean_nat_dec_lt(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
v___y_111_ = v_b_109_;
goto v___jp_110_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_le(v___x_121_, v___x_121_);
if (v___x_123_ == 0)
{
if (v___x_122_ == 0)
{
v___y_111_ = v_b_109_;
goto v___jp_110_;
}
else
{
size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_121_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_105_, v_snd_118_, v___x_124_, v___x_125_, v_b_109_);
v___y_111_ = v___x_126_;
goto v___jp_110_;
}
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_121_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_105_, v_snd_118_, v___x_127_, v___x_128_, v_b_109_);
v___y_111_ = v___x_129_;
goto v___jp_110_;
}
}
}
}
else
{
return v_b_109_;
}
v___jp_110_:
{
size_t v___x_112_; size_t v___x_113_; 
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_add(v_i_107_, v___x_112_);
v_i_107_ = v___x_113_;
v_b_109_ = v___y_111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___boxed(lean_object* v_pkgRoot_130_, lean_object* v_args_131_, lean_object* v_as_132_, lean_object* v_i_133_, lean_object* v_stop_134_, lean_object* v_b_135_){
_start:
{
size_t v_i_boxed_136_; size_t v_stop_boxed_137_; lean_object* v_res_138_; 
v_i_boxed_136_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_stop_boxed_137_ = lean_unbox_usize(v_stop_134_);
lean_dec(v_stop_134_);
v_res_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_130_, v_args_131_, v_as_132_, v_i_boxed_136_, v_stop_boxed_137_, v_b_135_);
lean_dec_ref(v_as_132_);
lean_dec_ref(v_args_131_);
lean_dec(v_pkgRoot_130_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_141_, lean_object* v_args_142_, lean_object* v_pkgRoot_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_146_ = l_Lean_Linter_getAllLints(v_env_141_);
v___x_147_ = lean_array_get_size(v___x_146_);
v___x_148_ = lean_nat_dec_lt(v___x_144_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec_ref(v___x_146_);
return v___x_145_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_le(v___x_147_, v___x_147_);
if (v___x_149_ == 0)
{
if (v___x_148_ == 0)
{
lean_dec_ref(v___x_146_);
return v___x_145_;
}
else
{
size_t v___x_150_; size_t v___x_151_; lean_object* v___x_152_; 
v___x_150_ = ((size_t)0ULL);
v___x_151_ = lean_usize_of_nat(v___x_147_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_143_, v_args_142_, v___x_146_, v___x_150_, v___x_151_, v___x_145_);
lean_dec_ref(v___x_146_);
return v___x_152_;
}
}
else
{
size_t v___x_153_; size_t v___x_154_; lean_object* v___x_155_; 
v___x_153_ = ((size_t)0ULL);
v___x_154_ = lean_usize_of_nat(v___x_147_);
v___x_155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_143_, v_args_142_, v___x_146_, v___x_153_, v___x_154_, v___x_145_);
lean_dec_ref(v___x_146_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_156_, lean_object* v_args_157_, lean_object* v_pkgRoot_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_156_, v_args_157_, v_pkgRoot_158_);
lean_dec(v_pkgRoot_158_);
lean_dec_ref(v_args_157_);
lean_dec_ref(v_env_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_enable_initializer_execution();
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_opts_164_, lean_object* v_opt_165_){
_start:
{
lean_object* v_name_166_; lean_object* v_defValue_167_; lean_object* v_map_168_; lean_object* v___x_169_; 
v_name_166_ = lean_ctor_get(v_opt_165_, 0);
v_defValue_167_ = lean_ctor_get(v_opt_165_, 1);
v_map_168_ = lean_ctor_get(v_opts_164_, 0);
v___x_169_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_168_, v_name_166_);
if (lean_obj_tag(v___x_169_) == 0)
{
uint8_t v___x_170_; 
v___x_170_ = lean_unbox(v_defValue_167_);
return v___x_170_;
}
else
{
lean_object* v_val_171_; 
v_val_171_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v___x_169_, 1);
if (lean_obj_tag(v_val_171_) == 1)
{
uint8_t v_v_172_; 
v_v_172_ = lean_ctor_get_uint8(v_val_171_, 0);
lean_dec_ref_known(v_val_171_, 0);
return v_v_172_;
}
else
{
uint8_t v___x_173_; 
lean_dec(v_val_171_);
v___x_173_ = lean_unbox(v_defValue_167_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_opts_174_, lean_object* v_opt_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(v_opts_174_, v_opt_175_);
lean_dec_ref(v_opt_175_);
lean_dec_ref(v_opts_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(lean_object* v_opts_178_, lean_object* v_opt_179_){
_start:
{
lean_object* v_name_180_; lean_object* v_defValue_181_; lean_object* v_map_182_; lean_object* v___x_183_; 
v_name_180_ = lean_ctor_get(v_opt_179_, 0);
v_defValue_181_ = lean_ctor_get(v_opt_179_, 1);
v_map_182_ = lean_ctor_get(v_opts_178_, 0);
v___x_183_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_182_, v_name_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_inc(v_defValue_181_);
return v_defValue_181_;
}
else
{
lean_object* v_val_184_; 
v_val_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_val_184_);
lean_dec_ref_known(v___x_183_, 1);
if (lean_obj_tag(v_val_184_) == 3)
{
lean_object* v_v_185_; 
v_v_185_ = lean_ctor_get(v_val_184_, 0);
lean_inc(v_v_185_);
lean_dec_ref_known(v_val_184_, 1);
return v_v_185_;
}
else
{
lean_dec(v_val_184_);
lean_inc(v_defValue_181_);
return v_defValue_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v_opts_186_, lean_object* v_opt_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(v_opts_186_, v_opt_187_);
lean_dec_ref(v_opt_187_);
lean_dec_ref(v_opts_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3(lean_object* v_s_189_){
_start:
{
lean_object* v___x_191_; lean_object* v_putStr_192_; lean_object* v___x_193_; 
v___x_191_ = lean_get_stdout();
v_putStr_192_ = lean_ctor_get(v___x_191_, 4);
lean_inc_ref(v_putStr_192_);
lean_dec_ref(v___x_191_);
v___x_193_ = lean_apply_2(v_putStr_192_, v_s_189_, lean_box(0));
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v_s_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v_s_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v___x_197_, lean_object* v_as_198_, size_t v_sz_199_, size_t v_i_200_, lean_object* v_b_201_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lean_usize_dec_lt(v_i_200_, v_sz_199_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_b_201_);
return v___x_204_;
}
else
{
lean_object* v_a_205_; lean_object* v_message_206_; lean_object* v___x_207_; uint8_t v_anyFailed_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_a_205_ = lean_array_uget_borrowed(v_as_198_, v_i_200_);
v_message_206_ = lean_ctor_get(v_a_205_, 1);
v___x_207_ = lean_unsigned_to_nat(0u);
v_anyFailed_208_ = lean_nat_dec_eq(v___x_197_, v___x_207_);
lean_inc_ref(v_message_206_);
v___x_209_ = l_Lean_SerialMessage_toString(v_message_206_, v_anyFailed_208_);
v___x_210_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; size_t v___x_212_; size_t v___x_213_; 
lean_dec_ref_known(v___x_210_, 1);
v___x_211_ = lean_box(0);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_200_, v___x_212_);
v_i_200_ = v___x_213_;
v_b_201_ = v___x_211_;
goto _start;
}
else
{
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v___x_215_, lean_object* v_as_216_, lean_object* v_sz_217_, lean_object* v_i_218_, lean_object* v_b_219_, lean_object* v___y_220_){
_start:
{
size_t v_sz_boxed_221_; size_t v_i_boxed_222_; lean_object* v_res_223_; 
v_sz_boxed_221_ = lean_unbox_usize(v_sz_217_);
lean_dec(v_sz_217_);
v_i_boxed_222_ = lean_unbox_usize(v_i_218_);
lean_dec(v_i_218_);
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_215_, v_as_216_, v_sz_boxed_221_, v_i_boxed_222_, v_b_219_);
lean_dec_ref(v_as_216_);
lean_dec(v___x_215_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_s_224_){
_start:
{
uint32_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = 10;
v___x_227_ = lean_string_push(v_s_224_, v___x_226_);
v___x_228_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_s_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v_s_229_);
return v_res_231_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(lean_object* v___x_232_, lean_object* v_as_233_, size_t v_i_234_, size_t v_stop_235_){
_start:
{
uint8_t v___x_236_; 
v___x_236_ = lean_usize_dec_eq(v_i_234_, v_stop_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v_snd_238_; lean_object* v_size_239_; lean_object* v___x_240_; uint8_t v___x_241_; uint8_t v___x_242_; 
v___x_237_ = lean_array_uget_borrowed(v_as_233_, v_i_234_);
v_snd_238_ = lean_ctor_get(v___x_237_, 1);
v_size_239_ = lean_ctor_get(v_snd_238_, 0);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = 1;
v___x_242_ = lean_nat_dec_eq(v_size_239_, v___x_240_);
if (v___x_242_ == 0)
{
return v___x_241_;
}
else
{
uint8_t v___x_243_; 
v___x_243_ = lean_nat_dec_eq(v___x_232_, v___x_240_);
if (v___x_243_ == 0)
{
size_t v___x_244_; size_t v___x_245_; 
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_add(v_i_234_, v___x_244_);
v_i_234_ = v___x_245_;
goto _start;
}
else
{
return v___x_241_;
}
}
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v___x_248_, lean_object* v_as_249_, lean_object* v_i_250_, lean_object* v_stop_251_){
_start:
{
size_t v_i_boxed_252_; size_t v_stop_boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_i_boxed_252_ = lean_unbox_usize(v_i_250_);
lean_dec(v_i_250_);
v_stop_boxed_253_ = lean_unbox_usize(v_stop_251_);
lean_dec(v_stop_251_);
v_res_254_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(v___x_248_, v_as_249_, v_i_boxed_252_, v_stop_boxed_253_);
lean_dec_ref(v_as_249_);
lean_dec(v___x_248_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = l_Lean_maxRecDepth;
v___x_270_ = l_Lean_Options_empty;
v___x_271_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_unsigned_to_nat(32u);
v___x_274_ = lean_mk_empty_array_with_capacity(v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12(void){
_start:
{
size_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = ((size_t)5ULL);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_unsigned_to_nat(32u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11);
v___x_281_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_277_);
lean_ctor_set(v___x_281_, 3, v___x_277_);
lean_ctor_set_usize(v___x_281_, 4, v___x_276_);
return v___x_281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = l_Lean_NameSet_empty;
v___x_288_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12);
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
lean_ctor_set(v___x_289_, 2, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = l_Lean_firstFrontendMacroScope;
v___x_292_ = lean_nat_add(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22(void){
_start:
{
lean_object* v___x_303_; uint64_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12);
v___x_304_ = 0ULL;
v___x_305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set_uint64(v___x_305_, sizeof(void*)*1, v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v_anyFailed_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12);
v___x_307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14);
v_anyFailed_308_ = 1;
v___x_309_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*3, v_anyFailed_308_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Lean_Options_empty;
v___x_312_ = l_Lean_Core_getMaxHeartbeats(v___x_311_);
return v___x_312_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = l_Lean_diagnostics;
v___x_314_ = l_Lean_Options_empty;
v___x_315_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(v___x_314_, v___x_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(lean_object* v___x_318_, lean_object* v_args_319_, uint8_t v_scope_320_, lean_object* v___y_321_, uint8_t v___y_322_, lean_object* v_as_323_, size_t v_sz_324_, size_t v_i_325_, uint8_t v_b_326_){
_start:
{
uint8_t v_a_329_; lean_object* v_msg_334_; lean_object* v_a_339_; lean_object* v___x_347_; uint8_t v_anyFailed_348_; uint8_t v_anyFailed_349_; lean_object* v___y_351_; uint8_t v___y_352_; uint8_t v_a_353_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; uint8_t v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___y_365_; lean_object* v___x_382_; lean_object* v_envLinterModule_383_; uint8_t v___x_384_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v_anyFailed_348_ = lean_nat_dec_eq(v___x_318_, v___x_347_);
v_anyFailed_349_ = 1;
v___x_382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4));
v_envLinterModule_383_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_383_, 0, v___x_382_);
lean_ctor_set_uint8(v_envLinterModule_383_, sizeof(void*)*1, v_anyFailed_348_);
lean_ctor_set_uint8(v_envLinterModule_383_, sizeof(void*)*1 + 1, v_anyFailed_349_);
lean_ctor_set_uint8(v_envLinterModule_383_, sizeof(void*)*1 + 2, v_anyFailed_348_);
v___x_384_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec_ref_known(v_envLinterModule_383_, 1);
v___x_385_ = lean_box(v_b_326_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; 
v___x_387_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; uint8_t v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; uint8_t v___y_397_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint32_t v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref_known(v___x_387_, 1);
v_a_388_ = lean_array_uget_borrowed(v_as_323_, v_i_325_);
lean_inc(v_a_388_);
v___x_418_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_418_, 0, v_a_388_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1, v_anyFailed_348_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1 + 1, v_anyFailed_349_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1 + 2, v_anyFailed_348_);
v___x_419_ = lean_unsigned_to_nat(2u);
v___x_420_ = lean_mk_empty_array_with_capacity(v___x_419_);
v___x_421_ = lean_array_push(v___x_420_, v___x_418_);
v___x_422_ = lean_array_push(v___x_421_, v_envLinterModule_383_);
v___x_423_ = l_Lean_Options_empty;
v___x_424_ = 1024;
v___x_425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__8));
v___x_426_ = 2;
v___x_427_ = lean_box(1);
v___x_428_ = l_Lean_importModules(v___x_422_, v___x_423_, v___x_424_, v___x_425_, v_anyFailed_348_, v_anyFailed_349_, v___x_426_, v___x_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___y_432_; uint8_t v___y_433_; uint8_t v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_496_; uint8_t v___y_497_; uint8_t v___y_498_; uint8_t v___y_519_; lean_object* v___x_546_; uint8_t v___y_548_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = l_Lean_Name_getRoot(v_a_388_);
v___x_546_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_a_429_, v_args_319_, v___x_430_);
v___x_575_ = lean_array_get_size(v___x_546_);
v___x_576_ = lean_nat_dec_eq(v___x_575_, v___x_347_);
if (v___x_576_ == 0)
{
v___y_548_ = v_anyFailed_349_;
goto v___jp_547_;
}
else
{
if (v_anyFailed_348_ == 0)
{
lean_dec_ref(v___x_546_);
v___y_519_ = v_anyFailed_348_;
goto v___jp_518_;
}
else
{
v___y_548_ = v_anyFailed_348_;
goto v___jp_547_;
}
}
v___jp_431_:
{
lean_object* v_fileName_437_; lean_object* v_fileMap_438_; lean_object* v_currRecDepth_439_; lean_object* v_ref_440_; lean_object* v_currNamespace_441_; lean_object* v_openDecls_442_; lean_object* v_initHeartbeats_443_; lean_object* v_maxHeartbeats_444_; lean_object* v_quotContext_445_; lean_object* v_currMacroScope_446_; lean_object* v_cancelTk_x3f_447_; uint8_t v_suppressElabErrors_448_; lean_object* v_inheritedTraceOptions_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_489_; 
v_fileName_437_ = lean_ctor_get(v___y_435_, 0);
v_fileMap_438_ = lean_ctor_get(v___y_435_, 1);
v_currRecDepth_439_ = lean_ctor_get(v___y_435_, 3);
v_ref_440_ = lean_ctor_get(v___y_435_, 5);
v_currNamespace_441_ = lean_ctor_get(v___y_435_, 6);
v_openDecls_442_ = lean_ctor_get(v___y_435_, 7);
v_initHeartbeats_443_ = lean_ctor_get(v___y_435_, 8);
v_maxHeartbeats_444_ = lean_ctor_get(v___y_435_, 9);
v_quotContext_445_ = lean_ctor_get(v___y_435_, 10);
v_currMacroScope_446_ = lean_ctor_get(v___y_435_, 11);
v_cancelTk_x3f_447_ = lean_ctor_get(v___y_435_, 12);
v_suppressElabErrors_448_ = lean_ctor_get_uint8(v___y_435_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_449_ = lean_ctor_get(v___y_435_, 13);
v_isSharedCheck_489_ = !lean_is_exclusive(v___y_435_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; lean_object* v_unused_491_; 
v_unused_490_ = lean_ctor_get(v___y_435_, 4);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v___y_435_, 2);
lean_dec(v_unused_491_);
v___x_451_ = v___y_435_;
v_isShared_452_ = v_isSharedCheck_489_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_inheritedTraceOptions_449_);
lean_inc(v_cancelTk_x3f_447_);
lean_inc(v_currMacroScope_446_);
lean_inc(v_quotContext_445_);
lean_inc(v_maxHeartbeats_444_);
lean_inc(v_initHeartbeats_443_);
lean_inc(v_openDecls_442_);
lean_inc(v_currNamespace_441_);
lean_inc(v_ref_440_);
lean_inc(v_currRecDepth_439_);
lean_inc(v_fileMap_438_);
lean_inc(v_fileName_437_);
lean_dec(v___y_435_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_489_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_430_, v___y_436_);
lean_dec(v___x_430_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v___x_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 4, v___x_455_);
lean_ctor_set(v___x_451_, 2, v___x_423_);
v___x_457_ = v___x_451_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_fileName_437_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_fileMap_438_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_currRecDepth_439_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_487_, 5, v_ref_440_);
lean_ctor_set(v_reuseFailAlloc_487_, 6, v_currNamespace_441_);
lean_ctor_set(v_reuseFailAlloc_487_, 7, v_openDecls_442_);
lean_ctor_set(v_reuseFailAlloc_487_, 8, v_initHeartbeats_443_);
lean_ctor_set(v_reuseFailAlloc_487_, 9, v_maxHeartbeats_444_);
lean_ctor_set(v_reuseFailAlloc_487_, 10, v_quotContext_445_);
lean_ctor_set(v_reuseFailAlloc_487_, 11, v_currMacroScope_446_);
lean_ctor_set(v_reuseFailAlloc_487_, 12, v_cancelTk_x3f_447_);
lean_ctor_set(v_reuseFailAlloc_487_, 13, v_inheritedTraceOptions_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_487_, sizeof(void*)*14 + 1, v_suppressElabErrors_448_);
v___x_457_ = v_reuseFailAlloc_487_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; 
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*14, v___y_434_);
v___x_458_ = l_Lean_Linter_EnvLinter_getChecks(v_scope_320_, v___y_321_, v___x_457_, v___y_436_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = lean_array_get_size(v_a_459_);
v___x_461_ = lean_nat_dec_eq(v___x_460_, v___x_347_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Linter_EnvLinter_lintCore(v_a_454_, v_a_459_, v___x_457_, v___y_436_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = lean_array_get_size(v_a_463_);
v___x_465_ = lean_nat_dec_lt(v___x_347_, v___x_464_);
if (v___x_465_ == 0)
{
v___y_390_ = v___x_457_;
v___y_391_ = v___x_460_;
v___y_392_ = v_a_463_;
v___y_393_ = v___y_432_;
v___y_394_ = v___y_433_;
v___y_395_ = v___y_436_;
v___y_396_ = v_a_454_;
v___y_397_ = v___x_461_;
goto v___jp_389_;
}
else
{
if (v___x_465_ == 0)
{
v___y_390_ = v___x_457_;
v___y_391_ = v___x_460_;
v___y_392_ = v_a_463_;
v___y_393_ = v___y_432_;
v___y_394_ = v___y_433_;
v___y_395_ = v___y_436_;
v___y_396_ = v_a_454_;
v___y_397_ = v___x_461_;
goto v___jp_389_;
}
else
{
size_t v___x_466_; size_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_464_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(v___x_460_, v_a_463_, v___x_466_, v___x_467_);
v___y_390_ = v___x_457_;
v___y_391_ = v___x_460_;
v___y_392_ = v_a_463_;
v___y_393_ = v___y_432_;
v___y_394_ = v___y_433_;
v___y_395_ = v___y_436_;
v___y_396_ = v_a_454_;
v___y_397_ = v___x_468_;
goto v___jp_389_;
}
}
}
else
{
lean_object* v_a_469_; 
lean_dec_ref(v___x_457_);
lean_dec(v_a_454_);
lean_dec(v___y_436_);
lean_dec(v___y_432_);
v_a_469_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_462_, 1);
v_a_339_ = v_a_469_;
goto v___jp_338_;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v_a_459_);
lean_dec_ref(v___x_457_);
lean_dec(v_a_454_);
lean_dec(v___y_436_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__10));
lean_inc(v_a_388_);
v___x_471_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_388_, v___x_461_);
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__6));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v___x_475_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_dec_ref_known(v___x_475_, 1);
v___y_351_ = v___y_432_;
v___y_352_ = v___y_433_;
v_a_353_ = v_anyFailed_348_;
goto v___jp_350_;
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_485_; 
lean_dec(v___y_432_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_485_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = lean_io_error_to_string(v_a_476_);
if (v_isShared_479_ == 0)
{
lean_ctor_set_tag(v___x_478_, 3);
lean_ctor_set(v___x_478_, 0, v___x_480_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_MessageData_ofFormat(v___x_482_);
v_msg_334_ = v___x_483_;
goto v___jp_333_;
}
}
}
}
}
else
{
lean_object* v_a_486_; 
lean_dec_ref(v___x_457_);
lean_dec(v_a_454_);
lean_dec(v___y_436_);
lean_dec(v___y_432_);
v_a_486_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_458_, 1);
v_a_339_ = v_a_486_;
goto v___jp_338_;
}
}
}
else
{
lean_object* v_a_488_; 
lean_del_object(v___x_451_);
lean_dec_ref(v_inheritedTraceOptions_449_);
lean_dec(v_cancelTk_x3f_447_);
lean_dec(v_currMacroScope_446_);
lean_dec(v_quotContext_445_);
lean_dec(v_maxHeartbeats_444_);
lean_dec(v_initHeartbeats_443_);
lean_dec(v_openDecls_442_);
lean_dec(v_currNamespace_441_);
lean_dec(v_ref_440_);
lean_dec(v_currRecDepth_439_);
lean_dec_ref(v_fileMap_438_);
lean_dec_ref(v_fileName_437_);
lean_dec(v___y_436_);
lean_dec(v___y_432_);
v_a_488_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_453_, 1);
v_a_339_ = v_a_488_;
goto v___jp_338_;
}
}
}
v___jp_492_:
{
if (v___y_498_ == 0)
{
lean_object* v___x_499_; lean_object* v_env_500_; lean_object* v_nextMacroScope_501_; lean_object* v_ngen_502_; lean_object* v_auxDeclNGen_503_; lean_object* v_traceState_504_; lean_object* v_messages_505_; lean_object* v_infoState_506_; lean_object* v_snapshotTasks_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_516_; 
v___x_499_ = lean_st_ref_take(v___y_493_);
v_env_500_ = lean_ctor_get(v___x_499_, 0);
v_nextMacroScope_501_ = lean_ctor_get(v___x_499_, 1);
v_ngen_502_ = lean_ctor_get(v___x_499_, 2);
v_auxDeclNGen_503_ = lean_ctor_get(v___x_499_, 3);
v_traceState_504_ = lean_ctor_get(v___x_499_, 4);
v_messages_505_ = lean_ctor_get(v___x_499_, 6);
v_infoState_506_ = lean_ctor_get(v___x_499_, 7);
v_snapshotTasks_507_ = lean_ctor_get(v___x_499_, 8);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_499_, 5);
lean_dec(v_unused_517_);
v___x_509_ = v___x_499_;
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snapshotTasks_507_);
lean_inc(v_infoState_506_);
lean_inc(v_messages_505_);
lean_inc(v_traceState_504_);
lean_inc(v_auxDeclNGen_503_);
lean_inc(v_ngen_502_);
lean_inc(v_nextMacroScope_501_);
lean_inc(v_env_500_);
lean_dec(v___x_499_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_516_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = l_Lean_Kernel_enableDiag(v_env_500_, v___y_497_);
lean_inc_ref(v___y_494_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 5, v___y_494_);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_ngen_502_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_auxDeclNGen_503_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_traceState_504_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v___y_494_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_messages_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_infoState_506_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_snapshotTasks_507_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_st_ref_set(v___y_493_, v___x_513_);
lean_inc(v___y_493_);
v___y_432_ = v___y_493_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_497_;
v___y_435_ = v___y_496_;
v___y_436_ = v___y_493_;
goto v___jp_431_;
}
}
}
else
{
lean_inc(v___y_493_);
v___y_432_ = v___y_493_;
v___y_433_ = v___y_495_;
v___y_434_ = v___y_497_;
v___y_435_ = v___y_496_;
v___y_436_ = v___y_493_;
goto v___jp_431_;
}
}
v___jp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_env_543_; uint8_t v___x_544_; uint8_t v___x_545_; 
v___x_520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15);
v___x_521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16);
v___x_522_ = lean_io_get_num_heartbeats();
v___x_523_ = l_Lean_firstFrontendMacroScope;
v___x_524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17);
v___x_525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__20));
v___x_526_ = lean_box(0);
v___x_527_ = lean_box(0);
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__21));
v___x_529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22);
v___x_530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23);
v___x_531_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_531_, 0, v_a_429_);
lean_ctor_set(v___x_531_, 1, v___x_524_);
lean_ctor_set(v___x_531_, 2, v___x_525_);
lean_ctor_set(v___x_531_, 3, v___x_528_);
lean_ctor_set(v___x_531_, 4, v___x_529_);
lean_ctor_set(v___x_531_, 5, v___x_520_);
lean_ctor_set(v___x_531_, 6, v___x_521_);
lean_ctor_set(v___x_531_, 7, v___x_530_);
lean_ctor_set(v___x_531_, 8, v___x_425_);
v___x_532_ = lean_st_mk_ref(v___x_531_);
v___x_533_ = l_Lean_inheritedTraceOptions;
v___x_534_ = lean_st_ref_get(v___x_533_);
v___x_535_ = lean_st_ref_get(v___x_532_);
v___x_536_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__24));
v___x_537_ = l_Lean_instInhabitedFileMap_default;
v___x_538_ = lean_unsigned_to_nat(1000u);
v___x_539_ = lean_box(0);
v___x_540_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25);
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_542_, 0, v___x_536_);
lean_ctor_set(v___x_542_, 1, v___x_537_);
lean_ctor_set(v___x_542_, 2, v___x_423_);
lean_ctor_set(v___x_542_, 3, v___x_347_);
lean_ctor_set(v___x_542_, 4, v___x_538_);
lean_ctor_set(v___x_542_, 5, v___x_539_);
lean_ctor_set(v___x_542_, 6, v___x_526_);
lean_ctor_set(v___x_542_, 7, v___x_527_);
lean_ctor_set(v___x_542_, 8, v___x_522_);
lean_ctor_set(v___x_542_, 9, v___x_540_);
lean_ctor_set(v___x_542_, 10, v___x_526_);
lean_ctor_set(v___x_542_, 11, v___x_523_);
lean_ctor_set(v___x_542_, 12, v___x_541_);
lean_ctor_set(v___x_542_, 13, v___x_534_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*14, v_anyFailed_348_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*14 + 1, v_anyFailed_348_);
v_env_543_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_env_543_);
lean_dec(v___x_535_);
v___x_544_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26);
v___x_545_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_543_);
lean_dec_ref(v_env_543_);
if (v___x_545_ == 0)
{
if (v___x_544_ == 0)
{
v___y_493_ = v___x_532_;
v___y_494_ = v___x_520_;
v___y_495_ = v___y_519_;
v___y_496_ = v___x_542_;
v___y_497_ = v___x_544_;
v___y_498_ = v___x_384_;
goto v___jp_492_;
}
else
{
v___y_493_ = v___x_532_;
v___y_494_ = v___x_520_;
v___y_495_ = v___y_519_;
v___y_496_ = v___x_542_;
v___y_497_ = v___x_544_;
v___y_498_ = v___x_545_;
goto v___jp_492_;
}
}
else
{
v___y_493_ = v___x_532_;
v___y_494_ = v___x_520_;
v___y_495_ = v___y_519_;
v___y_496_ = v___x_542_;
v___y_497_ = v___x_544_;
v___y_498_ = v___x_544_;
goto v___jp_492_;
}
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_549_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__27));
lean_inc(v_a_388_);
v___x_550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_388_, v___y_548_);
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__28));
v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
v___x_554_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; size_t v_sz_556_; size_t v___x_557_; lean_object* v___x_558_; 
lean_dec_ref_known(v___x_554_, 1);
v___x_555_ = lean_box(0);
v_sz_556_ = lean_array_size(v___x_546_);
v___x_557_ = ((size_t)0ULL);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_318_, v___x_546_, v_sz_556_, v___x_557_, v___x_555_);
lean_dec_ref(v___x_546_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_dec_ref_known(v___x_558_, 1);
v___y_519_ = v___y_548_;
goto v___jp_518_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v___x_430_);
lean_dec(v_a_429_);
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec_ref(v___x_546_);
lean_dec(v___x_430_);
lean_dec(v_a_429_);
v_a_567_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_554_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_554_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_428_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_428_);
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
v___jp_389_:
{
if (v___y_397_ == 0)
{
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
if (v___y_394_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5));
lean_inc(v_a_388_);
v___x_399_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_388_, v_anyFailed_349_);
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__6));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
v___x_403_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_dec_ref_known(v___x_403_, 1);
v___y_351_ = v___y_393_;
v___y_352_ = v___y_394_;
v_a_353_ = v___y_397_;
goto v___jp_350_;
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_413_; 
lean_dec(v___y_393_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_413_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_413_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_413_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_io_error_to_string(v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 3);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_412_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_MessageData_ofFormat(v___x_410_);
v_msg_334_ = v___x_411_;
goto v___jp_333_;
}
}
}
}
else
{
v___y_351_ = v___y_393_;
v___y_352_ = v___y_394_;
v_a_353_ = v___y_397_;
goto v___jp_350_;
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__7));
lean_inc(v_a_388_);
v___x_415_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_388_, v___y_397_);
v___x_416_ = lean_string_append(v___x_414_, v___x_415_);
lean_dec_ref(v___x_415_);
if (v___y_322_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 2;
v___y_356_ = v___y_390_;
v___y_357_ = v___y_391_;
v___y_358_ = v___y_393_;
v___y_359_ = v___y_392_;
v___y_360_ = v___y_394_;
v___y_361_ = v___y_397_;
v___y_362_ = v___y_395_;
v___y_363_ = v___x_416_;
v___y_364_ = v___y_396_;
v___y_365_ = v___x_417_;
goto v___jp_355_;
}
else
{
v___y_356_ = v___y_390_;
v___y_357_ = v___y_391_;
v___y_358_ = v___y_393_;
v___y_359_ = v___y_392_;
v___y_360_ = v___y_394_;
v___y_361_ = v___y_397_;
v___y_362_ = v___y_395_;
v___y_363_ = v___x_416_;
v___y_364_ = v___y_396_;
v___y_365_ = v_scope_320_;
goto v___jp_355_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref_known(v_envLinterModule_383_, 1);
v_a_585_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_387_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_387_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
v___jp_328_:
{
size_t v___x_330_; size_t v___x_331_; 
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_add(v_i_325_, v___x_330_);
v_i_325_ = v___x_331_;
v_b_326_ = v_a_329_;
goto _start;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l_Lean_MessageData_toString(v_msg_334_);
v___x_336_ = lean_mk_io_user_error(v___x_335_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
v___jp_338_:
{
if (lean_obj_tag(v_a_339_) == 0)
{
lean_object* v_msg_340_; 
v_msg_340_ = lean_ctor_get(v_a_339_, 1);
lean_inc_ref(v_msg_340_);
lean_dec_ref_known(v_a_339_, 2);
v_msg_334_ = v_msg_340_;
goto v___jp_333_;
}
else
{
lean_object* v_id_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_id_341_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_id_341_);
lean_dec_ref_known(v_a_339_, 2);
v___x_342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0));
v___x_343_ = l_Nat_reprFast(v_id_341_);
v___x_344_ = lean_string_append(v___x_342_, v___x_343_);
lean_dec_ref(v___x_343_);
v___x_345_ = lean_mk_io_user_error(v___x_344_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
v___jp_350_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_st_ref_get(v___y_351_);
lean_dec(v___y_351_);
lean_dec(v___x_354_);
if (v___y_352_ == 0)
{
if (v_a_353_ == 0)
{
v_a_329_ = v_b_326_;
goto v___jp_328_;
}
else
{
v_a_329_ = v_anyFailed_349_;
goto v___jp_328_;
}
}
else
{
v_a_329_ = v_anyFailed_349_;
goto v___jp_328_;
}
}
v___jp_355_:
{
uint8_t v___x_366_; lean_object* v___x_367_; 
v___x_366_ = 1;
v___x_367_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_359_, v___y_364_, v_anyFailed_349_, v___y_363_, v___y_365_, v___x_366_, v___y_357_, v_anyFailed_349_, v___y_356_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_356_);
lean_dec_ref(v___y_364_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = l_Lean_MessageData_toString(v_a_368_);
v___x_370_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_dec_ref_known(v___x_370_, 1);
v___y_351_ = v___y_358_;
v___y_352_ = v___y_360_;
v_a_353_ = v___y_361_;
goto v___jp_350_;
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_380_; 
lean_dec(v___y_358_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_380_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_380_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_380_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_io_error_to_string(v_a_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 3);
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_MessageData_ofFormat(v___x_377_);
v_msg_334_ = v___x_378_;
goto v___jp_333_;
}
}
}
}
else
{
lean_object* v_a_381_; 
lean_dec(v___y_358_);
v_a_381_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_367_, 1);
v_a_339_ = v_a_381_;
goto v___jp_338_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v___x_593_, lean_object* v_args_594_, lean_object* v_scope_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v_as_598_, lean_object* v_sz_599_, lean_object* v_i_600_, lean_object* v_b_601_, lean_object* v___y_602_){
_start:
{
uint8_t v_scope_boxed_603_; uint8_t v___y_7980__boxed_604_; size_t v_sz_boxed_605_; size_t v_i_boxed_606_; uint8_t v_b_boxed_607_; lean_object* v_res_608_; 
v_scope_boxed_603_ = lean_unbox(v_scope_595_);
v___y_7980__boxed_604_ = lean_unbox(v___y_597_);
v_sz_boxed_605_ = lean_unbox_usize(v_sz_599_);
lean_dec(v_sz_599_);
v_i_boxed_606_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_b_boxed_607_ = lean_unbox(v_b_601_);
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_593_, v_args_594_, v_scope_boxed_603_, v___y_596_, v___y_7980__boxed_604_, v_as_598_, v_sz_boxed_605_, v_i_boxed_606_, v_b_boxed_607_);
lean_dec_ref(v_as_598_);
lean_dec(v___y_596_);
lean_dec_ref(v_args_594_);
lean_dec(v___x_593_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7(lean_object* v_s_609_){
_start:
{
lean_object* v___x_611_; lean_object* v_putStr_612_; lean_object* v___x_613_; 
v___x_611_ = lean_get_stderr();
v_putStr_612_ = lean_ctor_get(v___x_611_, 4);
lean_inc_ref(v_putStr_612_);
lean_dec_ref(v___x_611_);
v___x_613_ = lean_apply_2(v_putStr_612_, v_s_609_, lean_box(0));
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7___boxed(lean_object* v_s_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7(v_s_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7(lean_object* v_s_617_){
_start:
{
uint32_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = 10;
v___x_620_ = lean_string_push(v_s_617_, v___x_619_);
v___x_621_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object* v_s_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7(v_s_622_);
return v_res_624_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_626_; lean_object* v___x_627_; 
v___x_626_ = 0;
v___x_627_ = lean_box_uint32(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_628_; lean_object* v___x_629_; 
v___x_628_ = 1;
v___x_629_ = lean_box_uint32(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_630_){
_start:
{
uint8_t v_scope_632_; lean_object* v_only_633_; lean_object* v_mods_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v_anyFailed_637_; 
v_scope_632_ = lean_ctor_get_uint8(v_args_630_, sizeof(void*)*2);
v_only_633_ = lean_ctor_get(v_args_630_, 0);
v_mods_634_ = lean_ctor_get(v_args_630_, 1);
lean_inc_ref(v_mods_634_);
v___x_635_ = lean_array_get_size(v_mods_634_);
v___x_636_ = lean_unsigned_to_nat(0u);
v_anyFailed_637_ = lean_nat_dec_eq(v___x_635_, v___x_636_);
if (v_anyFailed_637_ == 0)
{
lean_object* v___x_638_; uint8_t v___x_639_; lean_object* v___y_641_; 
v___x_638_ = lean_array_get_size(v_only_633_);
v___x_639_ = lean_nat_dec_eq(v___x_638_, v___x_636_);
if (v___x_639_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_inc_ref(v_only_633_);
v___x_667_ = lean_array_to_list(v_only_633_);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
v___y_641_ = v___x_668_;
goto v___jp_640_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
v___y_641_ = v___x_669_;
goto v___jp_640_;
}
v___jp_640_:
{
size_t v_sz_642_; size_t v___x_643_; lean_object* v___x_644_; 
v_sz_642_ = lean_array_size(v_mods_634_);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_635_, v_args_630_, v_scope_632_, v___y_641_, v___x_639_, v_mods_634_, v_sz_642_, v___x_643_, v_anyFailed_637_);
lean_dec_ref(v_mods_634_);
lean_dec(v___y_641_);
lean_dec_ref(v_args_630_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_658_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_658_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_658_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_658_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; 
v___x_649_ = lean_unbox(v_a_645_);
lean_dec(v_a_645_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_650_);
v___x_652_ = v___x_647_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_654_);
v___x_656_ = v___x_647_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_644_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_644_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec_ref(v_mods_634_);
lean_dec_ref(v_args_630_);
v___x_670_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_671_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7(v___x_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_671_, 0);
lean_dec(v_unused_680_);
v___x_673_ = v___x_671_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_dec(v___x_671_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_671_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_671_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
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
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lake_BuiltinLint_run(v_args_689_);
return v_res_691_;
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
