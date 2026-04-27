// Lean compiler output
// Module: Lake.CLI.BuiltinLint
// Imports: public import Lean.Linter.EnvLinter import Lean.CoreM import Lake.Config.Workspace
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
lean_object* lean_get_stderr();
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_get_stdout();
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_Options_empty;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_enable_initializer_execution();
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Linter_EnvLinter_getChecks(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__6;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__8;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__10;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__11;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__12;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__13_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__17;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__18;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-- Linting passed for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__20_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "in "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__21_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__22_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__23;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__24;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__25;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "-- No linters registered for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__26_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__6_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__6_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_BuiltinLint_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "lake lint: no modules specified for builtin linting"};
static const lean_object* l_Lake_BuiltinLint_run___closed__0 = (const lean_object*)&l_Lake_BuiltinLint_run___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_enable_initializer_execution();
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1___boxed(lean_object* v_a_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lake_CLI_BuiltinLint_0__Lake_BuiltinLint_run_unsafe__1();
return v_res_4_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(lean_object* v_opts_5_, lean_object* v_opt_6_){
_start:
{
lean_object* v_name_7_; lean_object* v_defValue_8_; lean_object* v_map_9_; lean_object* v___x_10_; 
v_name_7_ = lean_ctor_get(v_opt_6_, 0);
v_defValue_8_ = lean_ctor_get(v_opt_6_, 1);
v_map_9_ = lean_ctor_get(v_opts_5_, 0);
v___x_10_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_9_, v_name_7_);
if (lean_obj_tag(v___x_10_) == 0)
{
uint8_t v___x_11_; 
v___x_11_ = lean_unbox(v_defValue_8_);
return v___x_11_;
}
else
{
lean_object* v_val_12_; 
v_val_12_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_val_12_);
lean_dec_ref(v___x_10_);
if (lean_obj_tag(v_val_12_) == 1)
{
uint8_t v_v_13_; 
v_v_13_ = lean_ctor_get_uint8(v_val_12_, 0);
lean_dec_ref(v_val_12_);
return v_v_13_;
}
else
{
uint8_t v___x_14_; 
lean_dec(v_val_12_);
v___x_14_ = lean_unbox(v_defValue_8_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0___boxed(lean_object* v_opts_15_, lean_object* v_opt_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(v_opts_15_, v_opt_16_);
lean_dec_ref(v_opt_16_);
lean_dec_ref(v_opts_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(lean_object* v_opts_19_, lean_object* v_opt_20_){
_start:
{
lean_object* v_name_21_; lean_object* v_defValue_22_; lean_object* v_map_23_; lean_object* v___x_24_; 
v_name_21_ = lean_ctor_get(v_opt_20_, 0);
v_defValue_22_ = lean_ctor_get(v_opt_20_, 1);
v_map_23_ = lean_ctor_get(v_opts_19_, 0);
v___x_24_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_23_, v_name_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_inc(v_defValue_22_);
return v_defValue_22_;
}
else
{
lean_object* v_val_25_; 
v_val_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_val_25_);
lean_dec_ref(v___x_24_);
if (lean_obj_tag(v_val_25_) == 3)
{
lean_object* v_v_26_; 
v_v_26_ = lean_ctor_get(v_val_25_, 0);
lean_inc(v_v_26_);
lean_dec_ref(v_val_25_);
return v_v_26_;
}
else
{
lean_dec(v_val_25_);
lean_inc(v_defValue_22_);
return v_defValue_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1___boxed(lean_object* v_opts_27_, lean_object* v_opt_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(v_opts_27_, v_opt_28_);
lean_dec_ref(v_opt_28_);
lean_dec_ref(v_opts_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3(lean_object* v_s_30_){
_start:
{
lean_object* v___x_32_; lean_object* v_putStr_33_; lean_object* v___x_34_; 
v___x_32_ = lean_get_stdout();
v_putStr_33_ = lean_ctor_get(v___x_32_, 4);
lean_inc_ref(v_putStr_33_);
lean_dec_ref(v___x_32_);
v___x_34_ = lean_apply_2(v_putStr_33_, v_s_30_, lean_box(0));
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00Lake_BuiltinLint_run_spec__3___boxed(lean_object* v_s_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v_s_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2(lean_object* v_s_38_){
_start:
{
uint32_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = 10;
v___x_41_ = lean_string_push(v_s_38_, v___x_40_);
v___x_42_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00Lake_BuiltinLint_run_spec__2___boxed(lean_object* v_s_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v_s_43_);
return v_res_45_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(lean_object* v___x_46_, lean_object* v_as_47_, size_t v_i_48_, size_t v_stop_49_){
_start:
{
uint8_t v___x_50_; 
v___x_50_ = lean_usize_dec_eq(v_i_48_, v_stop_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v_snd_52_; lean_object* v_size_53_; lean_object* v___x_54_; uint8_t v___x_55_; uint8_t v___x_56_; 
v___x_51_ = lean_array_uget_borrowed(v_as_47_, v_i_48_);
v_snd_52_ = lean_ctor_get(v___x_51_, 1);
v_size_53_ = lean_ctor_get(v_snd_52_, 0);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = 1;
v___x_56_ = lean_nat_dec_eq(v_size_53_, v___x_54_);
if (v___x_56_ == 0)
{
return v___x_55_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = lean_nat_dec_eq(v___x_46_, v___x_54_);
if (v___x_57_ == 0)
{
size_t v___x_58_; size_t v___x_59_; 
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_add(v_i_48_, v___x_58_);
v_i_48_ = v___x_59_;
goto _start;
}
else
{
return v___x_55_;
}
}
}
else
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4___boxed(lean_object* v___x_62_, lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_){
_start:
{
size_t v_i_boxed_66_; size_t v_stop_boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v_i_boxed_66_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_67_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_res_68_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(v___x_62_, v_as_63_, v_i_boxed_66_, v_stop_boxed_67_);
lean_dec_ref(v_as_63_);
lean_dec(v___x_62_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__6(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_unsigned_to_nat(32u);
v___x_81_ = lean_mk_empty_array_with_capacity(v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7(void){
_start:
{
size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_83_ = ((size_t)5ULL);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_unsigned_to_nat(32u);
v___x_86_ = lean_mk_empty_array_with_capacity(v___x_85_);
v___x_87_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__6);
v___x_88_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_84_);
lean_ctor_set(v___x_88_, 3, v___x_84_);
lean_ctor_set_usize(v___x_88_, 4, v___x_83_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__8(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_89_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__8);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__10(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__11(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = l_Lean_NameSet_empty;
v___x_95_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7);
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
lean_ctor_set(v___x_96_, 2, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__12(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_unsigned_to_nat(1u);
v___x_98_ = l_Lean_firstFrontendMacroScope;
v___x_99_ = lean_nat_add(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__17(void){
_start:
{
lean_object* v___x_110_; uint64_t v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7);
v___x_111_ = 0ULL;
v___x_112_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set_uint64(v___x_112_, sizeof(void*)*1, v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__18(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v_anyFailed_115_; lean_object* v___x_116_; 
v___x_113_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__7);
v___x_114_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__9);
v_anyFailed_115_ = 1;
v___x_116_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
lean_ctor_set(v___x_116_, 2, v___x_113_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*3, v_anyFailed_115_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__23(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = l_Lean_Options_empty;
v___x_122_ = l_Lean_Core_getMaxHeartbeats(v___x_121_);
return v___x_122_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__24(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = l_Lean_diagnostics;
v___x_124_ = l_Lean_Options_empty;
v___x_125_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__0(v___x_124_, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__25(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = l_Lean_maxRecDepth;
v___x_127_ = l_Lean_Options_empty;
v___x_128_ = l_Lean_Option_get___at___00Lake_BuiltinLint_run_spec__1(v___x_127_, v___x_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(lean_object* v___x_130_, uint8_t v_scope_131_, lean_object* v___y_132_, uint8_t v___y_133_, lean_object* v_as_134_, size_t v_sz_135_, size_t v_i_136_, uint8_t v_b_137_){
_start:
{
uint8_t v_a_140_; lean_object* v_msg_145_; lean_object* v_a_150_; lean_object* v___x_158_; uint8_t v_anyFailed_159_; uint8_t v_anyFailed_160_; lean_object* v___x_161_; lean_object* v_envLinterModule_162_; uint8_t v___x_163_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v_anyFailed_159_ = lean_nat_dec_eq(v___x_130_, v___x_158_);
v_anyFailed_160_ = 1;
v___x_161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__4));
v_envLinterModule_162_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v_envLinterModule_162_, 0, v___x_161_);
lean_ctor_set_uint8(v_envLinterModule_162_, sizeof(void*)*1, v_anyFailed_159_);
lean_ctor_set_uint8(v_envLinterModule_162_, sizeof(void*)*1 + 1, v_anyFailed_160_);
lean_ctor_set_uint8(v_envLinterModule_162_, sizeof(void*)*1 + 2, v_anyFailed_159_);
v___x_163_ = lean_usize_dec_lt(v_i_136_, v_sz_135_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec_ref(v_envLinterModule_162_);
v___x_164_ = lean_box(v_b_137_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint32_t v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec_ref(v___x_166_);
v_a_167_ = lean_array_uget_borrowed(v_as_134_, v_i_136_);
lean_inc(v_a_167_);
v___x_168_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_168_, 0, v_a_167_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v_anyFailed_159_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1 + 1, v_anyFailed_160_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1 + 2, v_anyFailed_159_);
v___x_169_ = lean_unsigned_to_nat(2u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_array_push(v___x_170_, v___x_168_);
v___x_172_ = lean_array_push(v___x_171_, v_envLinterModule_162_);
v___x_173_ = l_Lean_Options_empty;
v___x_174_ = 1024;
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__5));
v___x_176_ = 2;
v___x_177_ = lean_box(1);
v___x_178_ = l_Lean_importModules(v___x_172_, v___x_173_, v___x_174_, v___x_175_, v_anyFailed_159_, v_anyFailed_160_, v___x_176_, v___x_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v_a_194_; uint8_t v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; uint8_t v___y_204_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; uint8_t v___y_227_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_env_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v_fileName_260_; lean_object* v_fileMap_261_; lean_object* v_currRecDepth_262_; lean_object* v_ref_263_; lean_object* v_currNamespace_264_; lean_object* v_openDecls_265_; lean_object* v_initHeartbeats_266_; lean_object* v_maxHeartbeats_267_; lean_object* v_quotContext_268_; lean_object* v_currMacroScope_269_; lean_object* v_cancelTk_x3f_270_; uint8_t v_suppressElabErrors_271_; lean_object* v_inheritedTraceOptions_272_; lean_object* v___y_273_; uint8_t v___y_309_; uint8_t v___x_329_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref(v___x_178_);
v___x_180_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__10);
v___x_181_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__11);
v___x_182_ = lean_io_get_num_heartbeats();
v___x_183_ = l_Lean_firstFrontendMacroScope;
v___x_184_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__12);
v___x_185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__15));
v___x_186_ = lean_box(0);
v___x_187_ = lean_box(0);
v___x_188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__16));
v___x_189_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__17);
v___x_190_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__18, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__18_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__18);
v___x_191_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_191_, 0, v_a_179_);
lean_ctor_set(v___x_191_, 1, v___x_184_);
lean_ctor_set(v___x_191_, 2, v___x_185_);
lean_ctor_set(v___x_191_, 3, v___x_188_);
lean_ctor_set(v___x_191_, 4, v___x_189_);
lean_ctor_set(v___x_191_, 5, v___x_180_);
lean_ctor_set(v___x_191_, 6, v___x_181_);
lean_ctor_set(v___x_191_, 7, v___x_190_);
lean_ctor_set(v___x_191_, 8, v___x_175_);
v___x_192_ = lean_st_mk_ref(v___x_191_);
v___x_248_ = l_Lean_inheritedTraceOptions;
v___x_249_ = lean_st_ref_get(v___x_248_);
v___x_250_ = lean_st_ref_get(v___x_192_);
v_env_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc_ref(v_env_251_);
lean_dec(v___x_250_);
v___x_252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__22));
v___x_253_ = l_Lean_instInhabitedFileMap_default;
v___x_254_ = lean_box(0);
v___x_255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__23, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__23_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__23);
v___x_256_ = lean_box(0);
v___x_257_ = l_Lean_Name_getRoot(v_a_167_);
v___x_258_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__24, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__24_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__24);
v___x_329_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_251_);
lean_dec_ref(v_env_251_);
if (v___x_329_ == 0)
{
if (v___x_258_ == 0)
{
v___y_309_ = v___x_163_;
goto v___jp_308_;
}
else
{
v___y_309_ = v___x_329_;
goto v___jp_308_;
}
}
else
{
v___y_309_ = v___x_258_;
goto v___jp_308_;
}
v___jp_193_:
{
lean_object* v___x_195_; 
v___x_195_ = lean_st_ref_get(v___x_192_);
lean_dec(v___x_192_);
lean_dec(v___x_195_);
if (v_a_194_ == 0)
{
v_a_140_ = v_b_137_;
goto v___jp_139_;
}
else
{
v_a_140_ = v_anyFailed_160_;
goto v___jp_139_;
}
}
v___jp_196_:
{
uint8_t v___x_205_; lean_object* v___x_206_; 
v___x_205_ = 1;
v___x_206_ = l_Lean_Linter_EnvLinter_formatLinterResults(v___y_199_, v___y_198_, v_anyFailed_160_, v___y_202_, v___y_204_, v___x_205_, v___y_203_, v_anyFailed_160_, v___y_201_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_201_);
lean_dec_ref(v___y_198_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v___x_206_);
v___x_208_ = l_Lean_MessageData_toString(v_a_207_);
v___x_209_ = l_IO_print___at___00Lake_BuiltinLint_run_spec__3(v___x_208_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_dec_ref(v___x_209_);
v_a_194_ = v___y_197_;
goto v___jp_193_;
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_219_; 
lean_dec(v___x_192_);
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_219_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_io_error_to_string(v_a_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set_tag(v___x_212_, 3);
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_218_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_MessageData_ofFormat(v___x_216_);
v_msg_145_ = v___x_217_;
goto v___jp_144_;
}
}
}
}
else
{
lean_object* v_a_220_; 
lean_dec(v___x_192_);
v_a_220_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_220_);
lean_dec_ref(v___x_206_);
v_a_150_ = v_a_220_;
goto v___jp_149_;
}
}
v___jp_221_:
{
if (v___y_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec_ref(v___y_222_);
v___x_228_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__19));
lean_inc(v_a_167_);
v___x_229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_167_, v_anyFailed_160_);
v___x_230_ = lean_string_append(v___x_228_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__20));
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
v___x_233_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_dec_ref(v___x_233_);
v_a_194_ = v___y_227_;
goto v___jp_193_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_243_; 
lean_dec(v___x_192_);
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_243_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_io_error_to_string(v_a_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 3);
lean_ctor_set(v___x_236_, 0, v___x_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_242_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_MessageData_ofFormat(v___x_240_);
v_msg_145_ = v___x_241_;
goto v___jp_144_;
}
}
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__21));
lean_inc(v_a_167_);
v___x_245_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_167_, v___y_227_);
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
lean_dec_ref(v___x_245_);
if (v___y_133_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = 2;
v___y_197_ = v___y_227_;
v___y_198_ = v___y_222_;
v___y_199_ = v___y_223_;
v___y_200_ = v___y_225_;
v___y_201_ = v___y_224_;
v___y_202_ = v___x_246_;
v___y_203_ = v___y_226_;
v___y_204_ = v___x_247_;
goto v___jp_196_;
}
else
{
v___y_197_ = v___y_227_;
v___y_198_ = v___y_222_;
v___y_199_ = v___y_223_;
v___y_200_ = v___y_225_;
v___y_201_ = v___y_224_;
v___y_202_ = v___x_246_;
v___y_203_ = v___y_226_;
v___y_204_ = v_scope_131_;
goto v___jp_196_;
}
}
}
v___jp_259_:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v___x_257_, v___y_273_);
lean_dec(v___x_257_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref(v___x_274_);
v___x_276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__25, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__25_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__25);
lean_inc(v_cancelTk_x3f_270_);
lean_inc(v_currMacroScope_269_);
lean_inc(v_quotContext_268_);
lean_inc(v_maxHeartbeats_267_);
lean_inc(v_openDecls_265_);
lean_inc(v_currNamespace_264_);
lean_inc(v_ref_263_);
lean_inc_ref(v_fileMap_261_);
lean_inc_ref(v_fileName_260_);
v___x_277_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_277_, 0, v_fileName_260_);
lean_ctor_set(v___x_277_, 1, v_fileMap_261_);
lean_ctor_set(v___x_277_, 2, v___x_173_);
lean_ctor_set(v___x_277_, 3, v_currRecDepth_262_);
lean_ctor_set(v___x_277_, 4, v___x_276_);
lean_ctor_set(v___x_277_, 5, v_ref_263_);
lean_ctor_set(v___x_277_, 6, v_currNamespace_264_);
lean_ctor_set(v___x_277_, 7, v_openDecls_265_);
lean_ctor_set(v___x_277_, 8, v_initHeartbeats_266_);
lean_ctor_set(v___x_277_, 9, v_maxHeartbeats_267_);
lean_ctor_set(v___x_277_, 10, v_quotContext_268_);
lean_ctor_set(v___x_277_, 11, v_currMacroScope_269_);
lean_ctor_set(v___x_277_, 12, v_cancelTk_x3f_270_);
lean_ctor_set(v___x_277_, 13, v_inheritedTraceOptions_272_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*14, v___x_258_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*14 + 1, v_suppressElabErrors_271_);
v___x_278_ = l_Lean_Linter_EnvLinter_getChecks(v_scope_131_, v___y_132_, v___x_277_, v___y_273_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref(v___x_278_);
v___x_280_ = lean_array_get_size(v_a_279_);
v___x_281_ = lean_nat_dec_eq(v___x_280_, v___x_158_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Linter_EnvLinter_lintCore(v_a_275_, v_a_279_, v___x_277_, v___y_273_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v___x_282_);
v___x_284_ = lean_array_get_size(v_a_283_);
v___x_285_ = lean_nat_dec_lt(v___x_158_, v___x_284_);
if (v___x_285_ == 0)
{
v___y_222_ = v_a_275_;
v___y_223_ = v_a_283_;
v___y_224_ = v___x_277_;
v___y_225_ = v___y_273_;
v___y_226_ = v___x_280_;
v___y_227_ = v___x_281_;
goto v___jp_221_;
}
else
{
if (v___x_285_ == 0)
{
v___y_222_ = v_a_275_;
v___y_223_ = v_a_283_;
v___y_224_ = v___x_277_;
v___y_225_ = v___y_273_;
v___y_226_ = v___x_280_;
v___y_227_ = v___x_281_;
goto v___jp_221_;
}
else
{
size_t v___x_286_; size_t v___x_287_; uint8_t v___x_288_; 
v___x_286_ = ((size_t)0ULL);
v___x_287_ = lean_usize_of_nat(v___x_284_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_BuiltinLint_run_spec__4(v___x_280_, v_a_283_, v___x_286_, v___x_287_);
v___y_222_ = v_a_275_;
v___y_223_ = v_a_283_;
v___y_224_ = v___x_277_;
v___y_225_ = v___y_273_;
v___y_226_ = v___x_280_;
v___y_227_ = v___x_288_;
goto v___jp_221_;
}
}
}
else
{
lean_object* v_a_289_; 
lean_dec_ref(v___x_277_);
lean_dec(v_a_275_);
lean_dec(v___y_273_);
lean_dec(v___x_192_);
v_a_289_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_289_);
lean_dec_ref(v___x_282_);
v_a_150_ = v_a_289_;
goto v___jp_149_;
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v_a_279_);
lean_dec_ref(v___x_277_);
lean_dec(v_a_275_);
lean_dec(v___y_273_);
v___x_290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__26));
lean_inc(v_a_167_);
v___x_291_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_167_, v___x_281_);
v___x_292_ = lean_string_append(v___x_290_, v___x_291_);
lean_dec_ref(v___x_291_);
v___x_293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__20));
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
v___x_295_ = l_IO_println___at___00Lake_BuiltinLint_run_spec__2(v___x_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_dec_ref(v___x_295_);
v_a_194_ = v_anyFailed_159_;
goto v___jp_193_;
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_305_; 
lean_dec(v___x_192_);
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_305_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_305_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = lean_io_error_to_string(v_a_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 3);
lean_ctor_set(v___x_298_, 0, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_300_);
v___x_302_ = v_reuseFailAlloc_304_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_MessageData_ofFormat(v___x_302_);
v_msg_145_ = v___x_303_;
goto v___jp_144_;
}
}
}
}
}
else
{
lean_object* v_a_306_; 
lean_dec_ref(v___x_277_);
lean_dec(v_a_275_);
lean_dec(v___y_273_);
lean_dec(v___x_192_);
v_a_306_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_306_);
lean_dec_ref(v___x_278_);
v_a_150_ = v_a_306_;
goto v___jp_149_;
}
}
else
{
lean_object* v_a_307_; 
lean_dec(v___y_273_);
lean_dec_ref(v_inheritedTraceOptions_272_);
lean_dec(v_initHeartbeats_266_);
lean_dec(v_currRecDepth_262_);
lean_dec(v___x_192_);
v_a_307_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_274_);
v_a_150_ = v_a_307_;
goto v___jp_149_;
}
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
lean_object* v___x_310_; lean_object* v_env_311_; lean_object* v_nextMacroScope_312_; lean_object* v_ngen_313_; lean_object* v_auxDeclNGen_314_; lean_object* v_traceState_315_; lean_object* v_messages_316_; lean_object* v_infoState_317_; lean_object* v_snapshotTasks_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_327_; 
v___x_310_ = lean_st_ref_take(v___x_192_);
v_env_311_ = lean_ctor_get(v___x_310_, 0);
v_nextMacroScope_312_ = lean_ctor_get(v___x_310_, 1);
v_ngen_313_ = lean_ctor_get(v___x_310_, 2);
v_auxDeclNGen_314_ = lean_ctor_get(v___x_310_, 3);
v_traceState_315_ = lean_ctor_get(v___x_310_, 4);
v_messages_316_ = lean_ctor_get(v___x_310_, 6);
v_infoState_317_ = lean_ctor_get(v___x_310_, 7);
v_snapshotTasks_318_ = lean_ctor_get(v___x_310_, 8);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_310_, 5);
lean_dec(v_unused_328_);
v___x_320_ = v___x_310_;
v_isShared_321_ = v_isSharedCheck_327_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_snapshotTasks_318_);
lean_inc(v_infoState_317_);
lean_inc(v_messages_316_);
lean_inc(v_traceState_315_);
lean_inc(v_auxDeclNGen_314_);
lean_inc(v_ngen_313_);
lean_inc(v_nextMacroScope_312_);
lean_inc(v_env_311_);
lean_dec(v___x_310_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_327_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = l_Lean_Kernel_enableDiag(v_env_311_, v___x_258_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 5, v___x_180_);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_nextMacroScope_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_ngen_313_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_auxDeclNGen_314_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_traceState_315_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v_messages_316_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_infoState_317_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_snapshotTasks_318_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_st_ref_set(v___x_192_, v___x_324_);
lean_inc(v___x_192_);
v_fileName_260_ = v___x_252_;
v_fileMap_261_ = v___x_253_;
v_currRecDepth_262_ = v___x_158_;
v_ref_263_ = v___x_254_;
v_currNamespace_264_ = v___x_186_;
v_openDecls_265_ = v___x_187_;
v_initHeartbeats_266_ = v___x_182_;
v_maxHeartbeats_267_ = v___x_255_;
v_quotContext_268_ = v___x_186_;
v_currMacroScope_269_ = v___x_183_;
v_cancelTk_x3f_270_ = v___x_256_;
v_suppressElabErrors_271_ = v_anyFailed_159_;
v_inheritedTraceOptions_272_ = v___x_249_;
v___y_273_ = v___x_192_;
goto v___jp_259_;
}
}
}
else
{
lean_inc(v___x_192_);
v_fileName_260_ = v___x_252_;
v_fileMap_261_ = v___x_253_;
v_currRecDepth_262_ = v___x_158_;
v_ref_263_ = v___x_254_;
v_currNamespace_264_ = v___x_186_;
v_openDecls_265_ = v___x_187_;
v_initHeartbeats_266_ = v___x_182_;
v_maxHeartbeats_267_ = v___x_255_;
v_quotContext_268_ = v___x_186_;
v_currMacroScope_269_ = v___x_183_;
v_cancelTk_x3f_270_ = v___x_256_;
v_suppressElabErrors_271_ = v_anyFailed_159_;
v_inheritedTraceOptions_272_ = v___x_249_;
v___y_273_ = v___x_192_;
goto v___jp_259_;
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_178_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_178_);
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
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
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
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec_ref(v_envLinterModule_162_);
v_a_338_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_166_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_166_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
v___jp_139_:
{
size_t v___x_141_; size_t v___x_142_; 
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_add(v_i_136_, v___x_141_);
v_i_136_ = v___x_142_;
v_b_137_ = v_a_140_;
goto _start;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = l_Lean_MessageData_toString(v_msg_145_);
v___x_147_ = lean_mk_io_user_error(v___x_146_);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
v___jp_149_:
{
if (lean_obj_tag(v_a_150_) == 0)
{
lean_object* v_msg_151_; 
v_msg_151_ = lean_ctor_get(v_a_150_, 1);
lean_inc_ref(v_msg_151_);
lean_dec_ref(v_a_150_);
v_msg_145_ = v_msg_151_;
goto v___jp_144_;
}
else
{
lean_object* v_id_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_id_152_ = lean_ctor_get(v_a_150_, 0);
lean_inc(v_id_152_);
lean_dec_ref(v_a_150_);
v___x_153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___closed__0));
v___x_154_ = l_Nat_reprFast(v_id_152_);
v___x_155_ = lean_string_append(v___x_153_, v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = lean_mk_io_user_error(v___x_155_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5___boxed(lean_object* v___x_346_, lean_object* v_scope_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v_as_350_, lean_object* v_sz_351_, lean_object* v_i_352_, lean_object* v_b_353_, lean_object* v___y_354_){
_start:
{
uint8_t v_scope_boxed_355_; uint8_t v___y_6754__boxed_356_; size_t v_sz_boxed_357_; size_t v_i_boxed_358_; uint8_t v_b_boxed_359_; lean_object* v_res_360_; 
v_scope_boxed_355_ = lean_unbox(v_scope_347_);
v___y_6754__boxed_356_ = lean_unbox(v___y_349_);
v_sz_boxed_357_ = lean_unbox_usize(v_sz_351_);
lean_dec(v_sz_351_);
v_i_boxed_358_ = lean_unbox_usize(v_i_352_);
lean_dec(v_i_352_);
v_b_boxed_359_ = lean_unbox(v_b_353_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_346_, v_scope_boxed_355_, v___y_348_, v___y_6754__boxed_356_, v_as_350_, v_sz_boxed_357_, v_i_boxed_358_, v_b_boxed_359_);
lean_dec_ref(v_as_350_);
lean_dec(v___y_348_);
lean_dec(v___x_346_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__6_spec__6(lean_object* v_s_361_){
_start:
{
lean_object* v___x_363_; lean_object* v_putStr_364_; lean_object* v___x_365_; 
v___x_363_ = lean_get_stderr();
v_putStr_364_ = lean_ctor_get(v___x_363_, 4);
lean_inc_ref(v_putStr_364_);
lean_dec_ref(v___x_363_);
v___x_365_ = lean_apply_2(v_putStr_364_, v_s_361_, lean_box(0));
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__6_spec__6___boxed(lean_object* v_s_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__6_spec__6(v_s_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__6(lean_object* v_s_369_){
_start:
{
uint32_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = 10;
v___x_372_ = lean_string_push(v_s_369_, v___x_371_);
v___x_373_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_BuiltinLint_run_spec__6_spec__6(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__6___boxed(lean_object* v_s_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__6(v_s_374_);
return v_res_376_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__1(void){
_start:
{
uint32_t v___x_378_; lean_object* v___x_379_; 
v___x_378_ = 0;
v___x_379_ = lean_box_uint32(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lake_BuiltinLint_run___boxed__const__2(void){
_start:
{
uint32_t v___x_380_; lean_object* v___x_381_; 
v___x_380_ = 1;
v___x_381_ = lean_box_uint32(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run(lean_object* v_args_382_){
_start:
{
uint8_t v_scope_384_; lean_object* v_only_385_; lean_object* v_mods_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v_anyFailed_389_; 
v_scope_384_ = lean_ctor_get_uint8(v_args_382_, sizeof(void*)*2);
v_only_385_ = lean_ctor_get(v_args_382_, 0);
lean_inc_ref(v_only_385_);
v_mods_386_ = lean_ctor_get(v_args_382_, 1);
lean_inc_ref(v_mods_386_);
lean_dec_ref(v_args_382_);
v___x_387_ = lean_array_get_size(v_mods_386_);
v___x_388_ = lean_unsigned_to_nat(0u);
v_anyFailed_389_ = lean_nat_dec_eq(v___x_387_, v___x_388_);
if (v_anyFailed_389_ == 0)
{
lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___y_393_; 
v___x_390_ = lean_array_get_size(v_only_385_);
v___x_391_ = lean_nat_dec_eq(v___x_390_, v___x_388_);
if (v___x_391_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_array_to_list(v_only_385_);
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
v___y_393_ = v___x_420_;
goto v___jp_392_;
}
else
{
lean_object* v___x_421_; 
lean_dec_ref(v_only_385_);
v___x_421_ = lean_box(0);
v___y_393_ = v___x_421_;
goto v___jp_392_;
}
v___jp_392_:
{
size_t v_sz_394_; size_t v___x_395_; lean_object* v___x_396_; 
v_sz_394_ = lean_array_size(v_mods_386_);
v___x_395_ = ((size_t)0ULL);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_BuiltinLint_run_spec__5(v___x_387_, v_scope_384_, v___y_393_, v___x_391_, v_mods_386_, v_sz_394_, v___x_395_, v_anyFailed_389_);
lean_dec_ref(v_mods_386_);
lean_dec(v___y_393_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_410_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_410_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_410_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_410_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; 
v___x_401_ = lean_unbox(v_a_397_);
lean_dec(v_a_397_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = l_Lake_BuiltinLint_run___boxed__const__1;
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_406_);
v___x_408_ = v___x_399_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_a_411_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_396_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_396_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; 
lean_dec_ref(v_mods_386_);
lean_dec_ref(v_only_385_);
v___x_422_ = ((lean_object*)(l_Lake_BuiltinLint_run___closed__0));
v___x_423_ = l_IO_eprintln___at___00Lake_BuiltinLint_run_spec__6(v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v___x_423_, 0);
lean_dec(v_unused_432_);
v___x_425_ = v___x_423_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_dec(v___x_423_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l_Lake_BuiltinLint_run___boxed__const__2;
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_423_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_423_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuiltinLint_run___boxed(lean_object* v_args_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lake_BuiltinLint_run(v_args_441_);
return v_res_443_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter(uint8_t builtin);
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
