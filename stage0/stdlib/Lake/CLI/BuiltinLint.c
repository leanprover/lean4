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
static const lean_string_object l_Lake_BuiltinLint_leanOptOverrides___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "clippy"};
static const lean_object* l_Lake_BuiltinLint_leanOptOverrides___closed__1 = (const lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__1_value;
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lake_BuiltinLint_leanOptOverrides___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__2_value_aux_0),((lean_object*)&l_Lake_BuiltinLint_leanOptOverrides___closed__1_value),LEAN_SCALAR_PTR_LITERAL(8, 147, 180, 72, 251, 158, 200, 109)}};
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
uint8_t v_scope_74_; lean_object* v_only_75_; lean_object* v___x_76_; uint8_t v___y_78_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v_scope_74_ = lean_ctor_get_uint8(v_args_63_, sizeof(void*)*2);
v_only_75_ = lean_ctor_get(v_args_63_, 0);
v___x_76_ = lean_array_uget_borrowed(v_as_64_, v_i_65_);
v___x_92_ = lean_array_get_size(v_only_75_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_nat_dec_eq(v___x_92_, v___x_93_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = lean_nat_dec_lt(v___x_93_, v___x_92_);
if (v___x_95_ == 0)
{
v___y_78_ = v___x_94_;
goto v___jp_77_;
}
else
{
if (v___x_95_ == 0)
{
v___y_78_ = v___x_94_;
goto v___jp_77_;
}
else
{
lean_object* v_linter_96_; size_t v___x_97_; size_t v___x_98_; uint8_t v___x_99_; 
v_linter_96_ = lean_ctor_get(v___x_76_, 0);
v___x_97_ = ((size_t)0ULL);
v___x_98_ = lean_usize_of_nat(v___x_92_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__0(v_linter_96_, v_only_75_, v___x_97_, v___x_98_);
v___y_78_ = v___x_99_;
goto v___jp_77_;
}
}
}
else
{
v___y_78_ = v___x_94_;
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
switch(v_scope_74_)
{
case 0:
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
case 1:
{
lean_object* v_linter_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_linter_87_ = lean_ctor_get(v___x_76_, 0);
v___x_88_ = ((lean_object*)(l_Lake_BuiltinLint_leanOptOverrides___closed__2));
v___x_89_ = l_Lean_Name_isPrefixOf(v___x_88_, v_linter_87_);
if (v___x_89_ == 0)
{
v___y_69_ = v_b_67_;
goto v___jp_68_;
}
else
{
lean_object* v___x_90_; 
lean_inc(v___x_76_);
v___x_90_ = lean_array_push(v_b_67_, v___x_76_);
v___y_69_ = v___x_90_;
goto v___jp_68_;
}
}
default: 
{
lean_object* v___x_91_; 
lean_inc(v___x_76_);
v___x_91_ = lean_array_push(v_b_67_, v___x_76_);
v___y_69_ = v___x_91_;
goto v___jp_68_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1___boxed(lean_object* v_args_100_, lean_object* v_as_101_, lean_object* v_i_102_, lean_object* v_stop_103_, lean_object* v_b_104_){
_start:
{
size_t v_i_boxed_105_; size_t v_stop_boxed_106_; lean_object* v_res_107_; 
v_i_boxed_105_ = lean_unbox_usize(v_i_102_);
lean_dec(v_i_102_);
v_stop_boxed_106_ = lean_unbox_usize(v_stop_103_);
lean_dec(v_stop_103_);
v_res_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_100_, v_as_101_, v_i_boxed_105_, v_stop_boxed_106_, v_b_104_);
lean_dec_ref(v_as_101_);
lean_dec_ref(v_args_100_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(lean_object* v_pkgRoot_108_, lean_object* v_args_109_, lean_object* v_as_110_, size_t v_i_111_, size_t v_stop_112_, lean_object* v_b_113_){
_start:
{
lean_object* v___y_115_; uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_eq(v_i_111_, v_stop_112_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; uint8_t v___x_123_; 
v___x_120_ = lean_array_uget_borrowed(v_as_110_, v_i_111_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
v___x_123_ = l_Lean_Name_isPrefixOf(v_pkgRoot_108_, v_fst_121_);
if (v___x_123_ == 0)
{
v___y_115_ = v_b_113_;
goto v___jp_114_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_array_get_size(v_snd_122_);
v___x_126_ = lean_nat_dec_lt(v___x_124_, v___x_125_);
if (v___x_126_ == 0)
{
v___y_115_ = v_b_113_;
goto v___jp_114_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_le(v___x_125_, v___x_125_);
if (v___x_127_ == 0)
{
if (v___x_126_ == 0)
{
v___y_115_ = v_b_113_;
goto v___jp_114_;
}
else
{
size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v___x_128_ = ((size_t)0ULL);
v___x_129_ = lean_usize_of_nat(v___x_125_);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_109_, v_snd_122_, v___x_128_, v___x_129_, v_b_113_);
v___y_115_ = v___x_130_;
goto v___jp_114_;
}
}
else
{
size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((size_t)0ULL);
v___x_132_ = lean_usize_of_nat(v___x_125_);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__1(v_args_109_, v_snd_122_, v___x_131_, v___x_132_, v_b_113_);
v___y_115_ = v___x_133_;
goto v___jp_114_;
}
}
}
}
else
{
return v_b_113_;
}
v___jp_114_:
{
size_t v___x_116_; size_t v___x_117_; 
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_add(v_i_111_, v___x_116_);
v_i_111_ = v___x_117_;
v_b_113_ = v___y_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2___boxed(lean_object* v_pkgRoot_134_, lean_object* v_args_135_, lean_object* v_as_136_, lean_object* v_i_137_, lean_object* v_stop_138_, lean_object* v_b_139_){
_start:
{
size_t v_i_boxed_140_; size_t v_stop_boxed_141_; lean_object* v_res_142_; 
v_i_boxed_140_ = lean_unbox_usize(v_i_137_);
lean_dec(v_i_137_);
v_stop_boxed_141_ = lean_unbox_usize(v_stop_138_);
lean_dec(v_stop_138_);
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_134_, v_args_135_, v_as_136_, v_i_boxed_140_, v_stop_boxed_141_, v_b_139_);
lean_dec_ref(v_as_136_);
lean_dec_ref(v_args_135_);
lean_dec(v_pkgRoot_134_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(lean_object* v_env_145_, lean_object* v_args_146_, lean_object* v_pkgRoot_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = ((lean_object*)(l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___closed__0));
v___x_150_ = l_Lean_Linter_getAllLints(v_env_145_);
v___x_151_ = lean_array_get_size(v___x_150_);
v___x_152_ = lean_nat_dec_lt(v___x_148_, v___x_151_);
if (v___x_152_ == 0)
{
lean_dec_ref(v___x_150_);
return v___x_149_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = lean_nat_dec_le(v___x_151_, v___x_151_);
if (v___x_153_ == 0)
{
if (v___x_152_ == 0)
{
lean_dec_ref(v___x_150_);
return v___x_149_;
}
else
{
size_t v___x_154_; size_t v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((size_t)0ULL);
v___x_155_ = lean_usize_of_nat(v___x_151_);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_147_, v_args_146_, v___x_150_, v___x_154_, v___x_155_, v___x_149_);
lean_dec_ref(v___x_150_);
return v___x_156_;
}
}
else
{
size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; 
v___x_157_ = ((size_t)0ULL);
v___x_158_ = lean_usize_of_nat(v___x_151_);
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints_spec__2(v_pkgRoot_147_, v_args_146_, v___x_150_, v___x_157_, v___x_158_, v___x_149_);
lean_dec_ref(v___x_150_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints___boxed(lean_object* v_env_160_, lean_object* v_args_161_, lean_object* v_pkgRoot_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_env_160_, v_args_161_, v_pkgRoot_162_);
lean_dec(v_pkgRoot_162_);
lean_dec_ref(v_args_161_);
lean_dec_ref(v_env_160_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_enable_initializer_execution();
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_opts_168_, lean_object* v_opt_169_){
_start:
{
lean_object* v_name_170_; lean_object* v_defValue_171_; lean_object* v_map_172_; lean_object* v___x_173_; 
v_name_170_ = lean_ctor_get(v_opt_169_, 0);
v_defValue_171_ = lean_ctor_get(v_opt_169_, 1);
v_map_172_ = lean_ctor_get(v_opts_168_, 0);
v___x_173_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_172_, v_name_170_);
if (lean_obj_tag(v___x_173_) == 0)
{
uint8_t v___x_174_; 
v___x_174_ = lean_unbox(v_defValue_171_);
return v___x_174_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_175_);
lean_dec_ref(v___x_173_);
if (lean_obj_tag(v_val_175_) == 1)
{
uint8_t v_v_176_; 
v_v_176_ = lean_ctor_get_uint8(v_val_175_, 0);
lean_dec_ref(v_val_175_);
return v_v_176_;
}
else
{
uint8_t v___x_177_; 
lean_dec(v_val_175_);
v___x_177_ = lean_unbox(v_defValue_171_);
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_opts_178_, lean_object* v_opt_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(v_opts_178_, v_opt_179_);
lean_dec_ref(v_opt_179_);
lean_dec_ref(v_opts_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(lean_object* v_opts_182_, lean_object* v_opt_183_){
_start:
{
lean_object* v_name_184_; lean_object* v_defValue_185_; lean_object* v_map_186_; lean_object* v___x_187_; 
v_name_184_ = lean_ctor_get(v_opt_183_, 0);
v_defValue_185_ = lean_ctor_get(v_opt_183_, 1);
v_map_186_ = lean_ctor_get(v_opts_182_, 0);
v___x_187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_186_, v_name_184_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_inc(v_defValue_185_);
return v_defValue_185_;
}
else
{
lean_object* v_val_188_; 
v_val_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_val_188_);
lean_dec_ref(v___x_187_);
if (lean_obj_tag(v_val_188_) == 3)
{
lean_object* v_v_189_; 
v_v_189_ = lean_ctor_get(v_val_188_, 0);
lean_inc(v_v_189_);
lean_dec_ref(v_val_188_);
return v_v_189_;
}
else
{
lean_dec(v_val_188_);
lean_inc(v_defValue_185_);
return v_defValue_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v_opts_190_, lean_object* v_opt_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(v_opts_190_, v_opt_191_);
lean_dec_ref(v_opt_191_);
lean_dec_ref(v_opts_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3(lean_object* v_s_193_){
_start:
{
lean_object* v___x_195_; lean_object* v_putStr_196_; lean_object* v___x_197_; 
v___x_195_ = lean_get_stdout();
v_putStr_196_ = lean_ctor_get(v___x_195_, 4);
lean_inc_ref(v_putStr_196_);
lean_dec_ref(v___x_195_);
v___x_197_ = lean_apply_2(v_putStr_196_, v_s_193_, lean_box(0));
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v_s_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v_s_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v___x_201_, lean_object* v_as_202_, size_t v_sz_203_, size_t v_i_204_, lean_object* v_b_205_){
_start:
{
uint8_t v___x_207_; 
v___x_207_ = lean_usize_dec_lt(v_i_204_, v_sz_203_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v_b_205_);
return v___x_208_;
}
else
{
lean_object* v_a_209_; lean_object* v_message_210_; lean_object* v___x_211_; uint8_t v_anyFailed_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_a_209_ = lean_array_uget_borrowed(v_as_202_, v_i_204_);
v_message_210_ = lean_ctor_get(v_a_209_, 1);
v___x_211_ = lean_unsigned_to_nat(0u);
v_anyFailed_212_ = lean_nat_dec_eq(v___x_201_, v___x_211_);
lean_inc_ref(v_message_210_);
v___x_213_ = l_Lean_SerialMessage_toString(v_message_210_, v_anyFailed_212_);
v___x_214_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v___x_215_; size_t v___x_216_; size_t v___x_217_; 
lean_dec_ref(v___x_214_);
v___x_215_ = lean_box(0);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_add(v_i_204_, v___x_216_);
v_i_204_ = v___x_217_;
v_b_205_ = v___x_215_;
goto _start;
}
else
{
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v___x_219_, lean_object* v_as_220_, lean_object* v_sz_221_, lean_object* v_i_222_, lean_object* v_b_223_, lean_object* v___y_224_){
_start:
{
size_t v_sz_boxed_225_; size_t v_i_boxed_226_; lean_object* v_res_227_; 
v_sz_boxed_225_ = lean_unbox_usize(v_sz_221_);
lean_dec(v_sz_221_);
v_i_boxed_226_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_219_, v_as_220_, v_sz_boxed_225_, v_i_boxed_226_, v_b_223_);
lean_dec_ref(v_as_220_);
lean_dec(v___x_219_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_s_228_){
_start:
{
uint32_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = 10;
v___x_231_ = lean_string_push(v_s_228_, v___x_230_);
v___x_232_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_s_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v_s_233_);
return v_res_235_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(lean_object* v___x_236_, lean_object* v_as_237_, size_t v_i_238_, size_t v_stop_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_eq(v_i_238_, v_stop_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v_snd_242_; lean_object* v_size_243_; lean_object* v___x_244_; uint8_t v___x_245_; uint8_t v___x_246_; 
v___x_241_ = lean_array_uget_borrowed(v_as_237_, v_i_238_);
v_snd_242_ = lean_ctor_get(v___x_241_, 1);
v_size_243_ = lean_ctor_get(v_snd_242_, 0);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = 1;
v___x_246_ = lean_nat_dec_eq(v_size_243_, v___x_244_);
if (v___x_246_ == 0)
{
return v___x_245_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = lean_nat_dec_eq(v___x_236_, v___x_244_);
if (v___x_247_ == 0)
{
size_t v___x_248_; size_t v___x_249_; 
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_add(v_i_238_, v___x_248_);
v_i_238_ = v___x_249_;
goto _start;
}
else
{
return v___x_245_;
}
}
}
else
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v___x_252_, lean_object* v_as_253_, lean_object* v_i_254_, lean_object* v_stop_255_){
_start:
{
size_t v_i_boxed_256_; size_t v_stop_boxed_257_; uint8_t v_res_258_; lean_object* v_r_259_; 
v_i_boxed_256_ = lean_unbox_usize(v_i_254_);
lean_dec(v_i_254_);
v_stop_boxed_257_ = lean_unbox_usize(v_stop_255_);
lean_dec(v_stop_255_);
v_res_258_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(v___x_252_, v_as_253_, v_i_boxed_256_, v_stop_boxed_257_);
lean_dec_ref(v_as_253_);
lean_dec(v___x_252_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_maxRecDepth;
v___x_274_ = l_Lean_Options_empty;
v___x_275_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(32u);
v___x_278_ = lean_mk_empty_array_with_capacity(v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12(void){
_start:
{
size_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = ((size_t)5ULL);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_unsigned_to_nat(32u);
v___x_283_ = lean_mk_empty_array_with_capacity(v___x_282_);
v___x_284_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__11);
v___x_285_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_281_);
lean_ctor_set(v___x_285_, 3, v___x_281_);
lean_ctor_set_usize(v___x_285_, 4, v___x_280_);
return v___x_285_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__13);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = l_Lean_NameSet_empty;
v___x_292_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12);
v___x_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_ctor_set(v___x_293_, 2, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = l_Lean_firstFrontendMacroScope;
v___x_296_ = lean_nat_add(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22(void){
_start:
{
lean_object* v___x_307_; uint64_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12);
v___x_308_ = 0ULL;
v___x_309_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set_uint64(v___x_309_, sizeof(void*)*1, v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v_anyFailed_312_; lean_object* v___x_313_; 
v___x_310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__12);
v___x_311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__14);
v_anyFailed_312_ = 1;
v___x_313_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_310_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*3, v_anyFailed_312_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = l_Lean_Options_empty;
v___x_316_ = l_Lean_Core_getMaxHeartbeats(v___x_315_);
return v___x_316_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = l_Lean_diagnostics;
v___x_318_ = l_Lean_Options_empty;
v___x_319_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(v___x_318_, v___x_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(lean_object* v___x_322_, lean_object* v_args_323_, uint8_t v_scope_324_, lean_object* v___y_325_, uint8_t v___y_326_, lean_object* v_as_327_, size_t v_sz_328_, size_t v_i_329_, uint8_t v_b_330_){
_start:
{
uint8_t v_a_333_; lean_object* v_msg_338_; lean_object* v_a_343_; lean_object* v___x_351_; uint8_t v_anyFailed_352_; uint8_t v_anyFailed_353_; lean_object* v___y_355_; uint8_t v___y_356_; uint8_t v_a_357_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; uint8_t v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; uint8_t v___y_367_; lean_object* v___y_368_; uint8_t v___y_369_; lean_object* v___x_386_; lean_object* v_envLinterModule_387_; uint8_t v___x_388_; 
v___x_351_ = lean_unsigned_to_nat(0u);
v_anyFailed_352_ = lean_nat_dec_eq(v___x_322_, v___x_351_);
v_anyFailed_353_ = 1;
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__4));
v_envLinterModule_387_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_387_, 0, v___x_386_);
lean_ctor_set_uint8(v_envLinterModule_387_, sizeof(void*)*1, v_anyFailed_352_);
lean_ctor_set_uint8(v_envLinterModule_387_, sizeof(void*)*1 + 1, v_anyFailed_353_);
lean_ctor_set_uint8(v_envLinterModule_387_, sizeof(void*)*1 + 2, v_anyFailed_352_);
v___x_388_ = lean_usize_dec_lt(v_i_329_, v_sz_328_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec_ref(v_envLinterModule_387_);
v___x_389_ = lean_box(v_b_330_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; uint8_t v___y_399_; lean_object* v___y_400_; uint8_t v___y_401_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint32_t v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref(v___x_391_);
v_a_392_ = lean_array_uget_borrowed(v_as_327_, v_i_329_);
lean_inc(v_a_392_);
v___x_422_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_422_, 0, v_a_392_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*1, v_anyFailed_352_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*1 + 1, v_anyFailed_353_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*1 + 2, v_anyFailed_352_);
v___x_423_ = lean_unsigned_to_nat(2u);
v___x_424_ = lean_mk_empty_array_with_capacity(v___x_423_);
v___x_425_ = lean_array_push(v___x_424_, v___x_422_);
v___x_426_ = lean_array_push(v___x_425_, v_envLinterModule_387_);
v___x_427_ = l_Lean_Options_empty;
v___x_428_ = 1024;
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__8));
v___x_430_ = 2;
v___x_431_ = lean_box(1);
v___x_432_ = l_Lean_importModules(v___x_426_, v___x_427_, v___x_428_, v___x_429_, v_anyFailed_352_, v_anyFailed_353_, v___x_430_, v___x_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; uint8_t v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_497_; uint8_t v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; uint8_t v___y_501_; uint8_t v___y_502_; uint8_t v___y_523_; lean_object* v___x_550_; uint8_t v___y_552_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = l_Lean_Name_getRoot(v_a_392_);
v___x_550_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_collectTextLints(v_a_433_, v_args_323_, v___x_434_);
v___x_579_ = lean_array_get_size(v___x_550_);
v___x_580_ = lean_nat_dec_eq(v___x_579_, v___x_351_);
if (v___x_580_ == 0)
{
v___y_552_ = v_anyFailed_353_;
goto v___jp_551_;
}
else
{
if (v_anyFailed_352_ == 0)
{
lean_dec_ref(v___x_550_);
v___y_523_ = v_anyFailed_352_;
goto v___jp_522_;
}
else
{
v___y_552_ = v_anyFailed_352_;
goto v___jp_551_;
}
}
v___jp_435_:
{
lean_object* v_fileName_441_; lean_object* v_fileMap_442_; lean_object* v_currRecDepth_443_; lean_object* v_ref_444_; lean_object* v_currNamespace_445_; lean_object* v_openDecls_446_; lean_object* v_initHeartbeats_447_; lean_object* v_maxHeartbeats_448_; lean_object* v_quotContext_449_; lean_object* v_currMacroScope_450_; lean_object* v_cancelTk_x3f_451_; uint8_t v_suppressElabErrors_452_; lean_object* v_inheritedTraceOptions_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_493_; 
v_fileName_441_ = lean_ctor_get(v___y_439_, 0);
v_fileMap_442_ = lean_ctor_get(v___y_439_, 1);
v_currRecDepth_443_ = lean_ctor_get(v___y_439_, 3);
v_ref_444_ = lean_ctor_get(v___y_439_, 5);
v_currNamespace_445_ = lean_ctor_get(v___y_439_, 6);
v_openDecls_446_ = lean_ctor_get(v___y_439_, 7);
v_initHeartbeats_447_ = lean_ctor_get(v___y_439_, 8);
v_maxHeartbeats_448_ = lean_ctor_get(v___y_439_, 9);
v_quotContext_449_ = lean_ctor_get(v___y_439_, 10);
v_currMacroScope_450_ = lean_ctor_get(v___y_439_, 11);
v_cancelTk_x3f_451_ = lean_ctor_get(v___y_439_, 12);
v_suppressElabErrors_452_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_453_ = lean_ctor_get(v___y_439_, 13);
v_isSharedCheck_493_ = !lean_is_exclusive(v___y_439_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_494_ = lean_ctor_get(v___y_439_, 4);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v___y_439_, 2);
lean_dec(v_unused_495_);
v___x_455_ = v___y_439_;
v_isShared_456_ = v_isSharedCheck_493_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_inheritedTraceOptions_453_);
lean_inc(v_cancelTk_x3f_451_);
lean_inc(v_currMacroScope_450_);
lean_inc(v_quotContext_449_);
lean_inc(v_maxHeartbeats_448_);
lean_inc(v_initHeartbeats_447_);
lean_inc(v_openDecls_446_);
lean_inc(v_currNamespace_445_);
lean_inc(v_ref_444_);
lean_inc(v_currRecDepth_443_);
lean_inc(v_fileMap_442_);
lean_inc(v_fileName_441_);
lean_dec(v___y_439_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_493_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_434_, v___y_440_);
lean_dec(v___x_434_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__9);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_459_);
lean_ctor_set(v___x_455_, 2, v___x_427_);
v___x_461_ = v___x_455_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_fileName_441_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_fileMap_442_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_currRecDepth_443_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_491_, 5, v_ref_444_);
lean_ctor_set(v_reuseFailAlloc_491_, 6, v_currNamespace_445_);
lean_ctor_set(v_reuseFailAlloc_491_, 7, v_openDecls_446_);
lean_ctor_set(v_reuseFailAlloc_491_, 8, v_initHeartbeats_447_);
lean_ctor_set(v_reuseFailAlloc_491_, 9, v_maxHeartbeats_448_);
lean_ctor_set(v_reuseFailAlloc_491_, 10, v_quotContext_449_);
lean_ctor_set(v_reuseFailAlloc_491_, 11, v_currMacroScope_450_);
lean_ctor_set(v_reuseFailAlloc_491_, 12, v_cancelTk_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_491_, 13, v_inheritedTraceOptions_453_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*14 + 1, v_suppressElabErrors_452_);
v___x_461_ = v_reuseFailAlloc_491_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*14, v___y_436_);
v___x_462_ = l_Lean_Linter_EnvLinter_getChecks(v_scope_324_, v___y_325_, v___x_461_, v___y_440_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v___x_462_);
v___x_464_ = lean_array_get_size(v_a_463_);
v___x_465_ = lean_nat_dec_eq(v___x_464_, v___x_351_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Linter_EnvLinter_lintCore(v_a_458_, v_a_463_, v___x_461_, v___y_440_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref(v___x_466_);
v___x_468_ = lean_array_get_size(v_a_467_);
v___x_469_ = lean_nat_dec_lt(v___x_351_, v___x_468_);
if (v___x_469_ == 0)
{
v___y_394_ = v___x_464_;
v___y_395_ = v___y_440_;
v___y_396_ = v___y_437_;
v___y_397_ = v_a_458_;
v___y_398_ = v___x_461_;
v___y_399_ = v___y_438_;
v___y_400_ = v_a_467_;
v___y_401_ = v___x_465_;
goto v___jp_393_;
}
else
{
if (v___x_469_ == 0)
{
v___y_394_ = v___x_464_;
v___y_395_ = v___y_440_;
v___y_396_ = v___y_437_;
v___y_397_ = v_a_458_;
v___y_398_ = v___x_461_;
v___y_399_ = v___y_438_;
v___y_400_ = v_a_467_;
v___y_401_ = v___x_465_;
goto v___jp_393_;
}
else
{
size_t v___x_470_; size_t v___x_471_; uint8_t v___x_472_; 
v___x_470_ = ((size_t)0ULL);
v___x_471_ = lean_usize_of_nat(v___x_468_);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(v___x_464_, v_a_467_, v___x_470_, v___x_471_);
v___y_394_ = v___x_464_;
v___y_395_ = v___y_440_;
v___y_396_ = v___y_437_;
v___y_397_ = v_a_458_;
v___y_398_ = v___x_461_;
v___y_399_ = v___y_438_;
v___y_400_ = v_a_467_;
v___y_401_ = v___x_472_;
goto v___jp_393_;
}
}
}
else
{
lean_object* v_a_473_; 
lean_dec_ref(v___x_461_);
lean_dec(v_a_458_);
lean_dec(v___y_440_);
lean_dec(v___y_437_);
v_a_473_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_466_);
v_a_343_ = v_a_473_;
goto v___jp_342_;
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_a_463_);
lean_dec_ref(v___x_461_);
lean_dec(v_a_458_);
lean_dec(v___y_440_);
v___x_474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__10));
lean_inc(v_a_392_);
v___x_475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_392_, v___x_465_);
v___x_476_ = lean_string_append(v___x_474_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__6));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v___x_479_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_dec_ref(v___x_479_);
v___y_355_ = v___y_437_;
v___y_356_ = v___y_438_;
v_a_357_ = v_anyFailed_352_;
goto v___jp_354_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_489_; 
lean_dec(v___y_437_);
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_489_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_io_error_to_string(v_a_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 3);
lean_ctor_set(v___x_482_, 0, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_488_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_MessageData_ofFormat(v___x_486_);
v_msg_338_ = v___x_487_;
goto v___jp_337_;
}
}
}
}
}
else
{
lean_object* v_a_490_; 
lean_dec_ref(v___x_461_);
lean_dec(v_a_458_);
lean_dec(v___y_440_);
lean_dec(v___y_437_);
v_a_490_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_490_);
lean_dec_ref(v___x_462_);
v_a_343_ = v_a_490_;
goto v___jp_342_;
}
}
}
else
{
lean_object* v_a_492_; 
lean_del_object(v___x_455_);
lean_dec_ref(v_inheritedTraceOptions_453_);
lean_dec(v_cancelTk_x3f_451_);
lean_dec(v_currMacroScope_450_);
lean_dec(v_quotContext_449_);
lean_dec(v_maxHeartbeats_448_);
lean_dec(v_initHeartbeats_447_);
lean_dec(v_openDecls_446_);
lean_dec(v_currNamespace_445_);
lean_dec(v_ref_444_);
lean_dec(v_currRecDepth_443_);
lean_dec_ref(v_fileMap_442_);
lean_dec_ref(v_fileName_441_);
lean_dec(v___y_440_);
lean_dec(v___y_437_);
v_a_492_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___x_457_);
v_a_343_ = v_a_492_;
goto v___jp_342_;
}
}
}
v___jp_496_:
{
if (v___y_502_ == 0)
{
lean_object* v___x_503_; lean_object* v_env_504_; lean_object* v_nextMacroScope_505_; lean_object* v_ngen_506_; lean_object* v_auxDeclNGen_507_; lean_object* v_traceState_508_; lean_object* v_messages_509_; lean_object* v_infoState_510_; lean_object* v_snapshotTasks_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_520_; 
v___x_503_ = lean_st_ref_take(v___y_500_);
v_env_504_ = lean_ctor_get(v___x_503_, 0);
v_nextMacroScope_505_ = lean_ctor_get(v___x_503_, 1);
v_ngen_506_ = lean_ctor_get(v___x_503_, 2);
v_auxDeclNGen_507_ = lean_ctor_get(v___x_503_, 3);
v_traceState_508_ = lean_ctor_get(v___x_503_, 4);
v_messages_509_ = lean_ctor_get(v___x_503_, 6);
v_infoState_510_ = lean_ctor_get(v___x_503_, 7);
v_snapshotTasks_511_ = lean_ctor_get(v___x_503_, 8);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v___x_503_, 5);
lean_dec(v_unused_521_);
v___x_513_ = v___x_503_;
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_snapshotTasks_511_);
lean_inc(v_infoState_510_);
lean_inc(v_messages_509_);
lean_inc(v_traceState_508_);
lean_inc(v_auxDeclNGen_507_);
lean_inc(v_ngen_506_);
lean_inc(v_nextMacroScope_505_);
lean_inc(v_env_504_);
lean_dec(v___x_503_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = l_Lean_Kernel_enableDiag(v_env_504_, v___y_498_);
lean_inc_ref(v___y_499_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 5, v___y_499_);
lean_ctor_set(v___x_513_, 0, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_nextMacroScope_505_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_ngen_506_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_auxDeclNGen_507_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_traceState_508_);
lean_ctor_set(v_reuseFailAlloc_519_, 5, v___y_499_);
lean_ctor_set(v_reuseFailAlloc_519_, 6, v_messages_509_);
lean_ctor_set(v_reuseFailAlloc_519_, 7, v_infoState_510_);
lean_ctor_set(v_reuseFailAlloc_519_, 8, v_snapshotTasks_511_);
v___x_517_ = v_reuseFailAlloc_519_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = lean_st_ref_set(v___y_500_, v___x_517_);
lean_inc(v___y_500_);
v___y_436_ = v___y_498_;
v___y_437_ = v___y_500_;
v___y_438_ = v___y_501_;
v___y_439_ = v___y_497_;
v___y_440_ = v___y_500_;
goto v___jp_435_;
}
}
}
else
{
lean_inc(v___y_500_);
v___y_436_ = v___y_498_;
v___y_437_ = v___y_500_;
v___y_438_ = v___y_501_;
v___y_439_ = v___y_497_;
v___y_440_ = v___y_500_;
goto v___jp_435_;
}
}
v___jp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_env_547_; uint8_t v___x_548_; uint8_t v___x_549_; 
v___x_524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__15);
v___x_525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__16);
v___x_526_ = lean_io_get_num_heartbeats();
v___x_527_ = l_Lean_firstFrontendMacroScope;
v___x_528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__17);
v___x_529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__20));
v___x_530_ = lean_box(0);
v___x_531_ = lean_box(0);
v___x_532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__21));
v___x_533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__22);
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__23);
v___x_535_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_535_, 0, v_a_433_);
lean_ctor_set(v___x_535_, 1, v___x_528_);
lean_ctor_set(v___x_535_, 2, v___x_529_);
lean_ctor_set(v___x_535_, 3, v___x_532_);
lean_ctor_set(v___x_535_, 4, v___x_533_);
lean_ctor_set(v___x_535_, 5, v___x_524_);
lean_ctor_set(v___x_535_, 6, v___x_525_);
lean_ctor_set(v___x_535_, 7, v___x_534_);
lean_ctor_set(v___x_535_, 8, v___x_429_);
v___x_536_ = lean_st_mk_ref(v___x_535_);
v___x_537_ = l_Lean_inheritedTraceOptions;
v___x_538_ = lean_st_ref_get(v___x_537_);
v___x_539_ = lean_st_ref_get(v___x_536_);
v___x_540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__24));
v___x_541_ = l_Lean_instInhabitedFileMap_default;
v___x_542_ = lean_unsigned_to_nat(1000u);
v___x_543_ = lean_box(0);
v___x_544_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__25);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_546_, 0, v___x_540_);
lean_ctor_set(v___x_546_, 1, v___x_541_);
lean_ctor_set(v___x_546_, 2, v___x_427_);
lean_ctor_set(v___x_546_, 3, v___x_351_);
lean_ctor_set(v___x_546_, 4, v___x_542_);
lean_ctor_set(v___x_546_, 5, v___x_543_);
lean_ctor_set(v___x_546_, 6, v___x_530_);
lean_ctor_set(v___x_546_, 7, v___x_531_);
lean_ctor_set(v___x_546_, 8, v___x_526_);
lean_ctor_set(v___x_546_, 9, v___x_544_);
lean_ctor_set(v___x_546_, 10, v___x_530_);
lean_ctor_set(v___x_546_, 11, v___x_527_);
lean_ctor_set(v___x_546_, 12, v___x_545_);
lean_ctor_set(v___x_546_, 13, v___x_538_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*14, v_anyFailed_352_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*14 + 1, v_anyFailed_352_);
v_env_547_ = lean_ctor_get(v___x_539_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_539_);
v___x_548_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__26);
v___x_549_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_547_);
lean_dec_ref(v_env_547_);
if (v___x_549_ == 0)
{
if (v___x_548_ == 0)
{
v___y_497_ = v___x_546_;
v___y_498_ = v___x_548_;
v___y_499_ = v___x_524_;
v___y_500_ = v___x_536_;
v___y_501_ = v___y_523_;
v___y_502_ = v___x_388_;
goto v___jp_496_;
}
else
{
v___y_497_ = v___x_546_;
v___y_498_ = v___x_548_;
v___y_499_ = v___x_524_;
v___y_500_ = v___x_536_;
v___y_501_ = v___y_523_;
v___y_502_ = v___x_549_;
goto v___jp_496_;
}
}
else
{
v___y_497_ = v___x_546_;
v___y_498_ = v___x_548_;
v___y_499_ = v___x_524_;
v___y_500_ = v___x_536_;
v___y_501_ = v___y_523_;
v___y_502_ = v___x_548_;
goto v___jp_496_;
}
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__27));
lean_inc(v_a_392_);
v___x_554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_392_, v___y_552_);
v___x_555_ = lean_string_append(v___x_553_, v___x_554_);
lean_dec_ref(v___x_554_);
v___x_556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__28));
v___x_557_ = lean_string_append(v___x_555_, v___x_556_);
v___x_558_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_557_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; size_t v_sz_560_; size_t v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v___x_558_);
v___x_559_ = lean_box(0);
v_sz_560_ = lean_array_size(v___x_550_);
v___x_561_ = ((size_t)0ULL);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_322_, v___x_550_, v_sz_560_, v___x_561_, v___x_559_);
lean_dec_ref(v___x_550_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_dec_ref(v___x_562_);
v___y_523_ = v___y_552_;
goto v___jp_522_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v___x_434_);
lean_dec(v_a_433_);
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v___x_550_);
lean_dec(v___x_434_);
lean_dec(v_a_433_);
v_a_571_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_558_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_558_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_432_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_432_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
v___jp_393_:
{
if (v___y_401_ == 0)
{
lean_dec_ref(v___y_400_);
lean_dec_ref(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_395_);
lean_dec(v___y_394_);
if (v___y_399_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__5));
lean_inc(v_a_392_);
v___x_403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_392_, v_anyFailed_353_);
v___x_404_ = lean_string_append(v___x_402_, v___x_403_);
lean_dec_ref(v___x_403_);
v___x_405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__6));
v___x_406_ = lean_string_append(v___x_404_, v___x_405_);
v___x_407_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_dec_ref(v___x_407_);
v___y_355_ = v___y_396_;
v___y_356_ = v___y_399_;
v_a_357_ = v___y_401_;
goto v___jp_354_;
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
lean_dec(v___y_396_);
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_417_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = lean_io_error_to_string(v_a_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 3);
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_416_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_MessageData_ofFormat(v___x_414_);
v_msg_338_ = v___x_415_;
goto v___jp_337_;
}
}
}
}
else
{
v___y_355_ = v___y_396_;
v___y_356_ = v___y_399_;
v_a_357_ = v___y_401_;
goto v___jp_354_;
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__7));
lean_inc(v_a_392_);
v___x_419_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_392_, v___y_401_);
v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
lean_dec_ref(v___x_419_);
if (v___y_326_ == 0)
{
uint8_t v___x_421_; 
v___x_421_ = 2;
v___y_360_ = v___x_420_;
v___y_361_ = v___y_395_;
v___y_362_ = v___y_394_;
v___y_363_ = v___y_396_;
v___y_364_ = v___y_399_;
v___y_365_ = v___y_398_;
v___y_366_ = v___y_397_;
v___y_367_ = v___y_401_;
v___y_368_ = v___y_400_;
v___y_369_ = v___x_421_;
goto v___jp_359_;
}
else
{
v___y_360_ = v___x_420_;
v___y_361_ = v___y_395_;
v___y_362_ = v___y_394_;
v___y_363_ = v___y_396_;
v___y_364_ = v___y_399_;
v___y_365_ = v___y_398_;
v___y_366_ = v___y_397_;
v___y_367_ = v___y_401_;
v___y_368_ = v___y_400_;
v___y_369_ = v_scope_324_;
goto v___jp_359_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_envLinterModule_387_);
v_a_589_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_391_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_391_);
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
v___jp_332_:
{
size_t v___x_334_; size_t v___x_335_; 
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_329_, v___x_334_);
v_i_329_ = v___x_335_;
v_b_330_ = v_a_333_;
goto _start;
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = l_Lean_MessageData_toString(v_msg_338_);
v___x_340_ = lean_mk_io_user_error(v___x_339_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
v___jp_342_:
{
if (lean_obj_tag(v_a_343_) == 0)
{
lean_object* v_msg_344_; 
v_msg_344_ = lean_ctor_get(v_a_343_, 1);
lean_inc_ref(v_msg_344_);
lean_dec_ref(v_a_343_);
v_msg_338_ = v_msg_344_;
goto v___jp_337_;
}
else
{
lean_object* v_id_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_id_345_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_id_345_);
lean_dec_ref(v_a_343_);
v___x_346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___closed__0));
v___x_347_ = l_Nat_reprFast(v_id_345_);
v___x_348_ = lean_string_append(v___x_346_, v___x_347_);
lean_dec_ref(v___x_347_);
v___x_349_ = lean_mk_io_user_error(v___x_348_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
v___jp_354_:
{
lean_object* v___x_358_; 
v___x_358_ = lean_st_ref_get(v___y_355_);
lean_dec(v___y_355_);
lean_dec(v___x_358_);
if (v___y_356_ == 0)
{
if (v_a_357_ == 0)
{
v_a_333_ = v_b_330_;
goto v___jp_332_;
}
else
{
v_a_333_ = v_anyFailed_353_;
goto v___jp_332_;
}
}
else
{
v_a_333_ = v_anyFailed_353_;
goto v___jp_332_;
}
}
v___jp_359_:
{
uint8_t v___x_370_; lean_object* v___x_371_; 
v___x_370_ = 1;
v___x_371_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_368_, v___y_366_, v_anyFailed_353_, v___y_360_, v___y_369_, v___x_370_, v___y_362_, v_anyFailed_353_, v___y_365_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_365_);
lean_dec_ref(v___y_366_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
v___x_373_ = l_Lean_MessageData_toString(v_a_372_);
v___x_374_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_373_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_dec_ref(v___x_374_);
v___y_355_ = v___y_363_;
v___y_356_ = v___y_364_;
v_a_357_ = v___y_367_;
goto v___jp_354_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_384_; 
lean_dec(v___y_363_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_384_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_io_error_to_string(v_a_375_);
if (v_isShared_378_ == 0)
{
lean_ctor_set_tag(v___x_377_, 3);
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_MessageData_ofFormat(v___x_381_);
v_msg_338_ = v___x_382_;
goto v___jp_337_;
}
}
}
}
else
{
lean_object* v_a_385_; 
lean_dec(v___y_363_);
v_a_385_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_371_);
v_a_343_ = v_a_385_;
goto v___jp_342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v___x_597_, lean_object* v_args_598_, lean_object* v_scope_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v_as_602_, lean_object* v_sz_603_, lean_object* v_i_604_, lean_object* v_b_605_, lean_object* v___y_606_){
_start:
{
uint8_t v_scope_boxed_607_; uint8_t v___y_7980__boxed_608_; size_t v_sz_boxed_609_; size_t v_i_boxed_610_; uint8_t v_b_boxed_611_; lean_object* v_res_612_; 
v_scope_boxed_607_ = lean_unbox(v_scope_599_);
v___y_7980__boxed_608_ = lean_unbox(v___y_601_);
v_sz_boxed_609_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v_i_boxed_610_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_b_boxed_611_ = lean_unbox(v_b_605_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_597_, v_args_598_, v_scope_boxed_607_, v___y_600_, v___y_7980__boxed_608_, v_as_602_, v_sz_boxed_609_, v_i_boxed_610_, v_b_boxed_611_);
lean_dec_ref(v_as_602_);
lean_dec(v___y_600_);
lean_dec_ref(v_args_598_);
lean_dec(v___x_597_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7(lean_object* v_s_613_){
_start:
{
lean_object* v___x_615_; lean_object* v_putStr_616_; lean_object* v___x_617_; 
v___x_615_ = lean_get_stderr();
v_putStr_616_ = lean_ctor_get(v___x_615_, 4);
lean_inc_ref(v_putStr_616_);
lean_dec_ref(v___x_615_);
v___x_617_ = lean_apply_2(v_putStr_616_, v_s_613_, lean_box(0));
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7___boxed(lean_object* v_s_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7(v_s_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7(lean_object* v_s_621_){
_start:
{
uint32_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = 10;
v___x_624_ = lean_string_push(v_s_621_, v___x_623_);
v___x_625_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__7_spec__7(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7___boxed(lean_object* v_s_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7(v_s_626_);
return v_res_628_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_630_; lean_object* v___x_631_; 
v___x_630_ = 0;
v___x_631_ = lean_box_uint32(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_632_; lean_object* v___x_633_; 
v___x_632_ = 1;
v___x_633_ = lean_box_uint32(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_634_){
_start:
{
uint8_t v_scope_636_; lean_object* v_only_637_; lean_object* v_mods_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v_anyFailed_641_; 
v_scope_636_ = lean_ctor_get_uint8(v_args_634_, sizeof(void*)*2);
v_only_637_ = lean_ctor_get(v_args_634_, 0);
v_mods_638_ = lean_ctor_get(v_args_634_, 1);
lean_inc_ref(v_mods_638_);
v___x_639_ = lean_array_get_size(v_mods_638_);
v___x_640_ = lean_unsigned_to_nat(0u);
v_anyFailed_641_ = lean_nat_dec_eq(v___x_639_, v___x_640_);
if (v_anyFailed_641_ == 0)
{
lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___y_645_; 
v___x_642_ = lean_array_get_size(v_only_637_);
v___x_643_ = lean_nat_dec_eq(v___x_642_, v___x_640_);
if (v___x_643_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_inc_ref(v_only_637_);
v___x_671_ = lean_array_to_list(v_only_637_);
v___x_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
v___y_645_ = v___x_672_;
goto v___jp_644_;
}
else
{
lean_object* v___x_673_; 
v___x_673_ = lean_box(0);
v___y_645_ = v___x_673_;
goto v___jp_644_;
}
v___jp_644_:
{
size_t v_sz_646_; size_t v___x_647_; lean_object* v___x_648_; 
v_sz_646_ = lean_array_size(v_mods_638_);
v___x_647_ = ((size_t)0ULL);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__6(v___x_639_, v_args_634_, v_scope_636_, v___y_645_, v___x_643_, v_mods_638_, v_sz_646_, v___x_647_, v_anyFailed_641_);
lean_dec_ref(v_mods_638_);
lean_dec(v___y_645_);
lean_dec_ref(v_args_634_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_662_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_662_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_662_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_662_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint8_t v___x_653_; 
v___x_653_ = lean_unbox(v_a_649_);
lean_dec(v_a_649_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_656_ = v___x_651_;
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
else
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_658_);
v___x_660_ = v___x_651_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_a_663_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_648_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_648_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec_ref(v_mods_638_);
lean_dec_ref(v_args_634_);
v___x_674_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_675_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__7(v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_675_, 0);
lean_dec(v_unused_684_);
v___x_677_ = v___x_675_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_dec(v___x_675_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
v_a_685_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_675_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_675_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lake_BuiltinLint_run(v_args_693_);
return v_res_695_;
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
