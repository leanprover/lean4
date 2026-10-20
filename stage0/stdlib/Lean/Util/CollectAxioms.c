// Lean compiler output
// Module: Lean.Util.CollectAxioms
// Imports: public import Lean.MonadEnv
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
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_once_cell_t l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0 = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value;
static lean_once_cell_t l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Util.CollectAxioms"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0 = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Util.CollectAxioms.0.Lean.CollectAxioms.collectAndGet"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1 = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "collectAndGet: '"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2 = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "' not in seen after collect"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3 = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0 = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value;
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 20, 155, 62, 160, 30, 19, 156)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "CollectAxioms"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 55, 253, 35, 47, 204, 39, 222)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(110, 123, 114, 100, 179, 32, 115, 58)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 81, 169, 218, 186, 106, 123, 199)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "exportedAxiomsExt"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 165, 200, 187, 116, 224, 61, 196)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value)} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt;
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = l_Lean_NameSet_empty;
v___x_2_ = lean_box(1);
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(lean_object* v_env_4_, lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_fst_8_; 
v___x_6_ = lean_obj_once(&l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0, &l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once, _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0);
v___x_7_ = lean_apply_2(v_x_5_, v_env_4_, v___x_6_);
v_fst_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_fst_8_);
lean_dec_ref(v___x_7_);
return v_fst_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM(lean_object* v_00_u03b1_9_, lean_object* v_env_10_, lean_object* v_x_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(v_env_10_, v_x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(lean_object* v_as_13_, size_t v_i_14_, size_t v_stop_15_, lean_object* v_b_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lean_usize_dec_eq(v_i_14_, v_stop_15_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; size_t v___x_20_; size_t v___x_21_; 
v___x_18_ = lean_array_uget_borrowed(v_as_13_, v_i_14_);
lean_inc(v___x_18_);
v___x_19_ = l_Lean_NameSet_insert(v_b_16_, v___x_18_);
v___x_20_ = ((size_t)1ULL);
v___x_21_ = lean_usize_add(v_i_14_, v___x_20_);
v_i_14_ = v___x_21_;
v_b_16_ = v___x_19_;
goto _start;
}
else
{
return v_b_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0___boxed(lean_object* v_as_23_, lean_object* v_i_24_, lean_object* v_stop_25_, lean_object* v_b_26_){
_start:
{
size_t v_i_boxed_27_; size_t v_stop_boxed_28_; lean_object* v_res_29_; 
v_i_boxed_27_ = lean_unbox_usize(v_i_24_);
lean_dec(v_i_24_);
v_stop_boxed_28_ = lean_unbox_usize(v_stop_25_);
lean_dec(v_stop_25_);
v_res_29_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_as_23_, v_i_boxed_27_, v_stop_boxed_28_, v_b_26_);
lean_dec_ref(v_as_23_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(lean_object* v_s_30_, lean_object* v_axs_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_array_get_size(v_axs_31_);
v___x_34_ = lean_nat_dec_lt(v___x_32_, v___x_33_);
if (v___x_34_ == 0)
{
return v_s_30_;
}
else
{
size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = ((size_t)0ULL);
v___x_36_ = lean_usize_of_nat(v___x_33_);
v___x_37_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_31_, v___x_35_, v___x_36_, v_s_30_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray___boxed(lean_object* v_s_38_, lean_object* v_axs_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_s_38_, v_axs_39_);
lean_dec_ref(v_axs_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(lean_object* v_init_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_k_43_; lean_object* v_l_44_; lean_object* v_r_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_k_43_ = lean_ctor_get(v_x_42_, 1);
lean_inc(v_k_43_);
v_l_44_ = lean_ctor_get(v_x_42_, 3);
lean_inc(v_l_44_);
v_r_45_ = lean_ctor_get(v_x_42_, 4);
lean_inc(v_r_45_);
lean_dec_ref_known(v_x_42_, 5);
v___x_46_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_41_, v_l_44_);
v___x_47_ = lean_array_push(v___x_46_, v_k_43_);
v_init_41_ = v___x_47_;
v_x_42_ = v_r_45_;
goto _start;
}
else
{
return v_init_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(lean_object* v_hi_49_, lean_object* v_pivot_50_, lean_object* v_as_51_, lean_object* v_i_52_, lean_object* v_k_53_){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = lean_nat_dec_lt(v_k_53_, v_hi_49_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_k_53_);
v___x_55_ = lean_array_fswap(v_as_51_, v_i_52_, v_hi_49_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v_i_52_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = lean_array_fget_borrowed(v_as_51_, v_k_53_);
v___x_58_ = l_Lean_Name_lt(v___x_57_, v_pivot_50_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_k_53_, v___x_59_);
lean_dec(v_k_53_);
v_k_53_ = v___x_60_;
goto _start;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_array_fswap(v_as_51_, v_i_52_, v_k_53_);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_add(v_i_52_, v___x_63_);
lean_dec(v_i_52_);
v___x_65_ = lean_nat_add(v_k_53_, v___x_63_);
lean_dec(v_k_53_);
v_as_51_ = v___x_62_;
v_i_52_ = v___x_64_;
v_k_53_ = v___x_65_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg___boxed(lean_object* v_hi_67_, lean_object* v_pivot_68_, lean_object* v_as_69_, lean_object* v_i_70_, lean_object* v_k_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_67_, v_pivot_68_, v_as_69_, v_i_70_, v_k_71_);
lean_dec(v_pivot_68_);
lean_dec(v_hi_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(lean_object* v_n_73_, lean_object* v_as_74_, lean_object* v_lo_75_, lean_object* v_hi_76_){
_start:
{
lean_object* v___y_78_; uint8_t v___x_88_; 
v___x_88_ = lean_nat_dec_lt(v_lo_75_, v_hi_76_);
if (v___x_88_ == 0)
{
lean_dec(v_lo_75_);
return v_as_74_;
}
else
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_mid_91_; lean_object* v___y_93_; lean_object* v___y_99_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_89_ = lean_nat_add(v_lo_75_, v_hi_76_);
v___x_90_ = lean_unsigned_to_nat(1u);
v_mid_91_ = lean_nat_shiftr(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_104_ = lean_array_fget_borrowed(v_as_74_, v_mid_91_);
v___x_105_ = lean_array_fget_borrowed(v_as_74_, v_lo_75_);
v___x_106_ = l_Lean_Name_lt(v___x_104_, v___x_105_);
if (v___x_106_ == 0)
{
v___y_99_ = v_as_74_;
goto v___jp_98_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_array_fswap(v_as_74_, v_lo_75_, v_mid_91_);
v___y_99_ = v___x_107_;
goto v___jp_98_;
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_94_ = lean_array_fget_borrowed(v___y_93_, v_mid_91_);
v___x_95_ = lean_array_fget_borrowed(v___y_93_, v_hi_76_);
v___x_96_ = l_Lean_Name_lt(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_dec(v_mid_91_);
v___y_78_ = v___y_93_;
goto v___jp_77_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = lean_array_fswap(v___y_93_, v_mid_91_, v_hi_76_);
lean_dec(v_mid_91_);
v___y_78_ = v___x_97_;
goto v___jp_77_;
}
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = lean_array_fget_borrowed(v___y_99_, v_hi_76_);
v___x_101_ = lean_array_fget_borrowed(v___y_99_, v_lo_75_);
v___x_102_ = l_Lean_Name_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
v___y_93_ = v___y_99_;
goto v___jp_92_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_array_fswap(v___y_99_, v_lo_75_, v_hi_76_);
v___y_93_ = v___x_103_;
goto v___jp_92_;
}
}
}
v___jp_77_:
{
lean_object* v_pivot_79_; lean_object* v___x_80_; lean_object* v_fst_81_; lean_object* v_snd_82_; uint8_t v___x_83_; 
v_pivot_79_ = lean_array_fget(v___y_78_, v_hi_76_);
lean_inc_n(v_lo_75_, 2);
v___x_80_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_76_, v_pivot_79_, v___y_78_, v_lo_75_, v_lo_75_);
lean_dec(v_pivot_79_);
v_fst_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_fst_81_);
v_snd_82_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_snd_82_);
lean_dec_ref(v___x_80_);
v___x_83_ = lean_nat_dec_le(v_hi_76_, v_fst_81_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_73_, v_snd_82_, v_lo_75_, v_fst_81_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_fst_81_, v___x_85_);
lean_dec(v_fst_81_);
v_as_74_ = v___x_84_;
v_lo_75_ = v___x_86_;
goto _start;
}
else
{
lean_dec(v_fst_81_);
lean_dec(v_lo_75_);
return v_snd_82_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg___boxed(lean_object* v_n_108_, lean_object* v_as_109_, lean_object* v_lo_110_, lean_object* v_hi_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_108_, v_as_109_, v_lo_110_, v_hi_111_);
lean_dec(v_hi_111_);
lean_dec(v_n_108_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(lean_object* v_extFind_x3f_115_, lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_, lean_object* v_b_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_fst_125_; lean_object* v_snd_126_; size_t v___x_127_; size_t v___x_128_; 
v___x_123_ = lean_array_uget_borrowed(v_as_116_, v_i_117_);
lean_inc(v___x_123_);
lean_inc_ref(v_extFind_x3f_115_);
v___x_124_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_115_, v___x_123_, v___y_120_, v___y_121_);
v_fst_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_fst_125_);
v_snd_126_ = lean_ctor_get(v___x_124_, 1);
lean_inc(v_snd_126_);
lean_dec_ref(v___x_124_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_i_117_, v___x_127_);
v_i_117_ = v___x_128_;
v_b_119_ = v_fst_125_;
v___y_121_ = v_snd_126_;
goto _start;
}
else
{
lean_object* v___x_130_; 
lean_dec_ref(v_extFind_x3f_115_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_b_119_);
lean_ctor_set(v___x_130_, 1, v___y_121_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(lean_object* v_extFind_x3f_131_, lean_object* v_e_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_135_ = l_Lean_Expr_getUsedConstants(v_e_132_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_array_get_size(v___x_135_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_nat_dec_lt(v___x_136_, v___x_137_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec_ref(v___x_135_);
lean_dec_ref(v_extFind_x3f_131_);
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___y_134_);
return v___x_140_;
}
else
{
size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_137_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_131_, v___x_135_, v___x_141_, v___x_142_, v___x_138_, v___y_133_, v___y_134_);
lean_dec_ref(v___x_135_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(lean_object* v_extFind_x3f_144_, lean_object* v_c_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; 
lean_inc_ref(v_extFind_x3f_144_);
lean_inc(v_c_145_);
lean_inc_ref(v_a_146_);
v___x_148_ = lean_apply_2(v_extFind_x3f_144_, v_a_146_, v_c_145_);
if (lean_obj_tag(v___x_148_) == 1)
{
lean_object* v_val_149_; lean_object* v_seen_150_; lean_object* v_axioms_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref(v_extFind_x3f_144_);
v_val_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_val_149_);
lean_dec_ref_known(v___x_148_, 1);
v_seen_150_ = lean_ctor_get(v_a_147_, 0);
v_axioms_151_ = lean_ctor_get(v_a_147_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_a_147_);
if (v_isSharedCheck_162_ == 0)
{
v___x_153_ = v_a_147_;
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_axioms_151_);
lean_inc(v_seen_150_);
lean_dec(v_a_147_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
lean_inc(v_val_149_);
v___x_155_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_145_, v_val_149_, v_seen_150_);
v___x_156_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_axioms_151_, v_val_149_);
lean_dec(v_val_149_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___x_156_);
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_156_);
v___x_158_ = v_reuseFailAlloc_161_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
return v___x_160_;
}
}
}
else
{
lean_object* v_seen_163_; lean_object* v_axioms_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_269_; 
lean_dec(v___x_148_);
v_seen_163_ = lean_ctor_get(v_a_147_, 0);
v_axioms_164_ = lean_ctor_get(v_a_147_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_a_147_);
if (v_isSharedCheck_269_ == 0)
{
v___x_166_ = v_a_147_;
v_isShared_167_ = v_isSharedCheck_269_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_axioms_164_);
lean_inc(v_seen_163_);
lean_dec(v_a_147_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_269_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_211_; lean_object* v_axioms_212_; lean_object* v___y_216_; lean_object* v___x_218_; 
v___x_218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_163_, v_c_145_);
if (lean_obj_tag(v___x_218_) == 1)
{
lean_object* v_val_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec(v_c_145_);
lean_dec_ref(v_extFind_x3f_144_);
v_val_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_axioms_164_, v_val_219_);
lean_dec(v_val_219_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_220_);
v___x_222_ = v___x_166_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_seen_163_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_225_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_box(0);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
return v___x_224_;
}
}
else
{
lean_object* v_checked_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
lean_dec(v___x_218_);
v_checked_226_ = lean_ctor_get(v_a_146_, 2);
v___x_227_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0));
lean_inc(v_c_145_);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_145_, v___x_227_, v_seen_163_);
v___x_229_ = l_Lean_NameSet_empty;
lean_inc(v___x_228_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_229_);
lean_ctor_set(v___x_166_, 0, v___x_228_);
v___x_231_ = v___x_166_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_268_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_inc_ref(v_checked_226_);
v___x_232_ = lean_task_get_own(v_checked_226_);
lean_inc(v_c_145_);
v___x_233_ = lean_environment_find(v___x_232_, v_c_145_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_dec(v___x_228_);
lean_dec_ref(v_extFind_x3f_144_);
v___y_211_ = v___x_231_;
v_axioms_212_ = v___x_229_;
goto v___jp_210_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_233_, 1);
switch(lean_obj_tag(v_val_234_))
{
case 0:
{
lean_object* v_val_235_; lean_object* v_toConstantVal_236_; lean_object* v_type_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v_snd_241_; 
lean_dec_ref(v___x_231_);
v_val_235_ = lean_ctor_get(v_val_234_, 0);
lean_inc_ref(v_val_235_);
lean_dec_ref_known(v_val_234_, 1);
v_toConstantVal_236_ = lean_ctor_get(v_val_235_, 0);
lean_inc_ref(v_toConstantVal_236_);
lean_dec_ref(v_val_235_);
v_type_237_ = lean_ctor_get(v_toConstantVal_236_, 2);
lean_inc_ref(v_type_237_);
lean_dec_ref(v_toConstantVal_236_);
lean_inc(v_c_145_);
v___x_238_ = l_Lean_NameSet_insert(v___x_229_, v_c_145_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_228_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_144_, v_type_237_, v_a_146_, v___x_239_);
v_snd_241_ = lean_ctor_get(v___x_240_, 1);
lean_inc(v_snd_241_);
lean_dec_ref(v___x_240_);
v___y_216_ = v_snd_241_;
goto v___jp_215_;
}
case 4:
{
lean_dec_ref_known(v_val_234_, 1);
lean_dec(v___x_228_);
lean_dec_ref(v_extFind_x3f_144_);
v___y_211_ = v___x_231_;
v_axioms_212_ = v___x_229_;
goto v___jp_210_;
}
case 5:
{
lean_object* v_val_242_; lean_object* v_toConstantVal_243_; lean_object* v_ctors_244_; lean_object* v_type_245_; lean_object* v___x_246_; lean_object* v_snd_247_; lean_object* v___x_248_; lean_object* v_snd_249_; 
lean_dec(v___x_228_);
v_val_242_ = lean_ctor_get(v_val_234_, 0);
lean_inc_ref(v_val_242_);
lean_dec_ref_known(v_val_234_, 1);
v_toConstantVal_243_ = lean_ctor_get(v_val_242_, 0);
lean_inc_ref(v_toConstantVal_243_);
v_ctors_244_ = lean_ctor_get(v_val_242_, 4);
lean_inc(v_ctors_244_);
lean_dec_ref(v_val_242_);
v_type_245_ = lean_ctor_get(v_toConstantVal_243_, 2);
lean_inc_ref(v_type_245_);
lean_dec_ref(v_toConstantVal_243_);
lean_inc_ref(v_extFind_x3f_144_);
v___x_246_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_144_, v_type_245_, v_a_146_, v___x_231_);
v_snd_247_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_snd_247_);
lean_dec_ref(v___x_246_);
v___x_248_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_144_, v_ctors_244_, v_a_146_, v_snd_247_);
v_snd_249_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_snd_249_);
lean_dec_ref(v___x_248_);
v___y_216_ = v_snd_249_;
goto v___jp_215_;
}
case 6:
{
lean_object* v_val_250_; lean_object* v_toConstantVal_251_; lean_object* v_type_252_; lean_object* v___x_253_; lean_object* v_snd_254_; 
lean_dec(v___x_228_);
v_val_250_ = lean_ctor_get(v_val_234_, 0);
lean_inc_ref(v_val_250_);
lean_dec_ref_known(v_val_234_, 1);
v_toConstantVal_251_ = lean_ctor_get(v_val_250_, 0);
lean_inc_ref(v_toConstantVal_251_);
lean_dec_ref(v_val_250_);
v_type_252_ = lean_ctor_get(v_toConstantVal_251_, 2);
lean_inc_ref(v_type_252_);
lean_dec_ref(v_toConstantVal_251_);
v___x_253_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_144_, v_type_252_, v_a_146_, v___x_231_);
v_snd_254_ = lean_ctor_get(v___x_253_, 1);
lean_inc(v_snd_254_);
lean_dec_ref(v___x_253_);
v___y_216_ = v_snd_254_;
goto v___jp_215_;
}
case 7:
{
lean_object* v_val_255_; lean_object* v_toConstantVal_256_; lean_object* v_type_257_; lean_object* v___x_258_; lean_object* v_snd_259_; 
lean_dec(v___x_228_);
v_val_255_ = lean_ctor_get(v_val_234_, 0);
lean_inc_ref(v_val_255_);
lean_dec_ref_known(v_val_234_, 1);
v_toConstantVal_256_ = lean_ctor_get(v_val_255_, 0);
lean_inc_ref(v_toConstantVal_256_);
lean_dec_ref(v_val_255_);
v_type_257_ = lean_ctor_get(v_toConstantVal_256_, 2);
lean_inc_ref(v_type_257_);
lean_dec_ref(v_toConstantVal_256_);
v___x_258_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_144_, v_type_257_, v_a_146_, v___x_231_);
v_snd_259_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_snd_259_);
lean_dec_ref(v___x_258_);
v___y_216_ = v_snd_259_;
goto v___jp_215_;
}
default: 
{
lean_object* v_val_260_; lean_object* v_toConstantVal_261_; lean_object* v_value_262_; lean_object* v_type_263_; lean_object* v___x_264_; lean_object* v_snd_265_; lean_object* v___x_266_; lean_object* v_snd_267_; 
lean_dec(v___x_228_);
v_val_260_ = lean_ctor_get(v_val_234_, 0);
lean_inc_ref(v_val_260_);
lean_dec(v_val_234_);
v_toConstantVal_261_ = lean_ctor_get(v_val_260_, 0);
lean_inc_ref(v_toConstantVal_261_);
v_value_262_ = lean_ctor_get(v_val_260_, 1);
lean_inc_ref(v_value_262_);
lean_dec_ref(v_val_260_);
v_type_263_ = lean_ctor_get(v_toConstantVal_261_, 2);
lean_inc_ref(v_type_263_);
lean_dec_ref(v_toConstantVal_261_);
lean_inc_ref(v_extFind_x3f_144_);
v___x_264_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_144_, v_type_263_, v_a_146_, v___x_231_);
v_snd_265_ = lean_ctor_get(v___x_264_, 1);
lean_inc(v_snd_265_);
lean_dec_ref(v___x_264_);
v___x_266_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_144_, v_value_262_, v_a_146_, v_snd_265_);
v_snd_267_ = lean_ctor_get(v___x_266_, 1);
lean_inc(v_snd_267_);
lean_dec_ref(v___x_266_);
v___y_216_ = v_snd_267_;
goto v___jp_215_;
}
}
}
}
}
v___jp_168_:
{
lean_object* v_seen_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_182_; 
v_seen_171_ = lean_ctor_get(v___y_169_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___y_169_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v___y_169_, 1);
lean_dec(v_unused_183_);
v___x_173_ = v___y_169_;
v_isShared_174_ = v_isSharedCheck_182_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_seen_171_);
lean_dec(v___y_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_182_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_175_ = lean_box(0);
lean_inc_ref(v___y_170_);
v___x_176_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_145_, v___y_170_, v_seen_171_);
v___x_177_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_axioms_164_, v___y_170_);
lean_dec_ref(v___y_170_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 1, v___x_177_);
lean_ctor_set(v___x_173_, 0, v___x_176_);
v___x_179_ = v___x_173_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_181_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_175_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
return v___x_180_;
}
}
}
v___jp_184_:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v___y_186_, v___y_188_, v___y_185_, v___y_189_);
lean_dec(v___y_189_);
lean_dec(v___y_186_);
v___y_169_ = v___y_187_;
v___y_170_ = v___x_190_;
goto v___jp_168_;
}
v___jp_191_:
{
uint8_t v___x_197_; 
v___x_197_ = lean_nat_dec_le(v___y_196_, v___y_192_);
if (v___x_197_ == 0)
{
lean_dec(v___y_192_);
lean_inc(v___y_196_);
v___y_185_ = v___y_196_;
v___y_186_ = v___y_193_;
v___y_187_ = v___y_194_;
v___y_188_ = v___y_195_;
v___y_189_ = v___y_196_;
goto v___jp_184_;
}
else
{
v___y_185_ = v___y_196_;
v___y_186_ = v___y_193_;
v___y_187_ = v___y_194_;
v___y_188_ = v___y_195_;
v___y_189_ = v___y_192_;
goto v___jp_184_;
}
}
v___jp_198_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_202_ = lean_mk_empty_array_with_capacity(v___y_201_);
lean_dec(v___y_201_);
v___x_203_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v___x_202_, v___y_199_);
v___x_204_ = lean_array_get_size(v___x_203_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_sub(v___x_204_, v___x_207_);
v___x_209_ = lean_nat_dec_le(v___x_205_, v___x_208_);
if (v___x_209_ == 0)
{
lean_inc(v___x_208_);
v___y_192_ = v___x_208_;
v___y_193_ = v___x_204_;
v___y_194_ = v___y_200_;
v___y_195_ = v___x_203_;
v___y_196_ = v___x_208_;
goto v___jp_191_;
}
else
{
v___y_192_ = v___x_208_;
v___y_193_ = v___x_204_;
v___y_194_ = v___y_200_;
v___y_195_ = v___x_203_;
v___y_196_ = v___x_205_;
goto v___jp_191_;
}
}
else
{
v___y_169_ = v___y_200_;
v___y_170_ = v___x_203_;
goto v___jp_168_;
}
}
v___jp_210_:
{
if (lean_obj_tag(v_axioms_212_) == 0)
{
lean_object* v_size_213_; 
v_size_213_ = lean_ctor_get(v_axioms_212_, 0);
lean_inc(v_size_213_);
v___y_199_ = v_axioms_212_;
v___y_200_ = v___y_211_;
v___y_201_ = v_size_213_;
goto v___jp_198_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___y_199_ = v_axioms_212_;
v___y_200_ = v___y_211_;
v___y_201_ = v___x_214_;
goto v___jp_198_;
}
}
v___jp_215_:
{
lean_object* v_axioms_217_; 
v_axioms_217_ = lean_ctor_get(v___y_216_, 1);
lean_inc(v_axioms_217_);
v___y_211_ = v___y_216_;
v_axioms_212_ = v_axioms_217_;
goto v___jp_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(lean_object* v_extFind_x3f_270_, lean_object* v_as_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
if (lean_obj_tag(v_as_271_) == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref(v_extFind_x3f_270_);
v___x_274_ = lean_box(0);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___y_273_);
return v___x_275_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_278_; lean_object* v_snd_279_; 
v_head_276_ = lean_ctor_get(v_as_271_, 0);
lean_inc(v_head_276_);
v_tail_277_ = lean_ctor_get(v_as_271_, 1);
lean_inc(v_tail_277_);
lean_dec_ref_known(v_as_271_, 2);
lean_inc_ref(v_extFind_x3f_270_);
v___x_278_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_270_, v_head_276_, v___y_272_, v___y_273_);
v_snd_279_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_snd_279_);
lean_dec_ref(v___x_278_);
v_as_271_ = v_tail_277_;
v___y_273_ = v_snd_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3___boxed(lean_object* v_extFind_x3f_281_, lean_object* v_as_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_281_, v_as_282_, v___y_283_, v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0___boxed(lean_object* v_extFind_x3f_286_, lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_, lean_object* v_b_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
size_t v_i_boxed_293_; size_t v_stop_boxed_294_; lean_object* v_res_295_; 
v_i_boxed_293_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_294_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_286_, v_as_287_, v_i_boxed_293_, v_stop_boxed_294_, v_b_290_, v___y_291_, v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec_ref(v_as_287_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0___boxed(lean_object* v_extFind_x3f_296_, lean_object* v_e_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_296_, v_e_297_, v___y_298_, v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___boxed(lean_object* v_extFind_x3f_301_, lean_object* v_c_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_301_, v_c_302_, v_a_303_, v_a_304_);
lean_dec_ref(v_a_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1(lean_object* v_init_306_, lean_object* v_t_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_306_, v_t_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(lean_object* v_n_309_, lean_object* v_as_310_, lean_object* v_lo_311_, lean_object* v_hi_312_, lean_object* v_w_313_, lean_object* v_hlo_314_, lean_object* v_hhi_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_309_, v_as_310_, v_lo_311_, v_hi_312_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___boxed(lean_object* v_n_317_, lean_object* v_as_318_, lean_object* v_lo_319_, lean_object* v_hi_320_, lean_object* v_w_321_, lean_object* v_hlo_322_, lean_object* v_hhi_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(v_n_317_, v_as_318_, v_lo_319_, v_hi_320_, v_w_321_, v_hlo_322_, v_hhi_323_);
lean_dec(v_hi_320_);
lean_dec(v_n_317_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(lean_object* v_n_325_, lean_object* v_lo_326_, lean_object* v_hi_327_, lean_object* v_hhi_328_, lean_object* v_pivot_329_, lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_k_332_, lean_object* v_ilo_333_, lean_object* v_ik_334_, lean_object* v_w_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_327_, v_pivot_329_, v_as_330_, v_i_331_, v_k_332_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___boxed(lean_object* v_n_337_, lean_object* v_lo_338_, lean_object* v_hi_339_, lean_object* v_hhi_340_, lean_object* v_pivot_341_, lean_object* v_as_342_, lean_object* v_i_343_, lean_object* v_k_344_, lean_object* v_ilo_345_, lean_object* v_ik_346_, lean_object* v_w_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(v_n_337_, v_lo_338_, v_hi_339_, v_hhi_340_, v_pivot_341_, v_as_342_, v_i_343_, v_k_344_, v_ilo_345_, v_ik_346_, v_w_347_);
lean_dec(v_pivot_341_);
lean_dec(v_hi_339_);
lean_dec(v_lo_338_);
lean_dec(v_n_337_);
return v_res_348_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Array_instInhabited___redArg();
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___f_360_; lean_object* v___f_361_; lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___f_382_; lean_object* v___x_981__overap_383_; lean_object* v___x_384_; 
v___f_360_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0));
v___f_361_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1));
v___f_362_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2));
v___f_363_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3));
v___f_364_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4));
v___f_365_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5));
v___f_366_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6));
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___f_360_);
lean_ctor_set(v___x_367_, 1, v___f_361_);
v___x_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v___f_362_);
lean_ctor_set(v___x_368_, 2, v___f_363_);
lean_ctor_set(v___x_368_, 3, v___f_364_);
lean_ctor_set(v___x_368_, 4, v___f_365_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___f_366_);
lean_inc_ref_n(v___x_369_, 6);
v___f_370_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_370_, 0, v___x_369_);
v___f_371_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_371_, 0, v___x_369_);
v___f_372_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_372_, 0, v___x_369_);
v___f_373_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_373_, 0, v___x_369_);
v___x_374_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_374_, 0, lean_box(0));
lean_closure_set(v___x_374_, 1, lean_box(0));
lean_closure_set(v___x_374_, 2, v___x_369_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___f_370_);
v___x_376_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_376_, 0, lean_box(0));
lean_closure_set(v___x_376_, 1, lean_box(0));
lean_closure_set(v___x_376_, 2, v___x_369_);
v___x_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
lean_ctor_set(v___x_377_, 2, v___f_371_);
lean_ctor_set(v___x_377_, 3, v___f_372_);
lean_ctor_set(v___x_377_, 4, v___f_373_);
v___x_378_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_378_, 0, lean_box(0));
lean_closure_set(v___x_378_, 1, lean_box(0));
lean_closure_set(v___x_378_, 2, v___x_369_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_obj_once(&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7, &l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once, _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7);
v___x_381_ = l_instInhabitedOfMonad___redArg(v___x_379_, v___x_380_);
v___f_382_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_382_, 0, v___x_381_);
v___x_981__overap_383_ = lean_panic_fn_borrowed(v___f_382_, v_msg_357_);
lean_dec_ref(v___f_382_);
lean_inc_ref(v___y_358_);
v___x_384_ = lean_apply_2(v___x_981__overap_383_, v___y_358_, v___y_359_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___boxed(lean_object* v_msg_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v_msg_385_, v___y_386_, v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(lean_object* v_extFind_x3f_393_, lean_object* v_c_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_397_; lean_object* v_snd_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_420_; 
lean_inc(v_c_394_);
v___x_397_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_393_, v_c_394_, v_a_395_, v_a_396_);
v_snd_398_ = lean_ctor_get(v___x_397_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v___x_397_, 0);
lean_dec(v_unused_421_);
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_420_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_snd_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_420_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_seen_402_; lean_object* v___x_403_; 
v_seen_402_ = lean_ctor_get(v_snd_398_, 0);
v___x_403_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_402_, v_c_394_);
if (lean_obj_tag(v___x_403_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_406_; 
lean_dec(v_c_394_);
v_val_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v___x_403_, 1);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_val_404_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_val_404_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_snd_398_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v___x_403_);
lean_del_object(v___x_400_);
v___x_408_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0));
v___x_409_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1));
v___x_410_ = lean_unsigned_to_nat(81u);
v___x_411_ = lean_unsigned_to_nat(41u);
v___x_412_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2));
v___x_413_ = 1;
v___x_414_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_394_, v___x_413_);
v___x_415_ = lean_string_append(v___x_412_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = l_mkPanicMessageWithDecl(v___x_408_, v___x_409_, v___x_410_, v___x_411_, v___x_417_);
lean_dec_ref(v___x_417_);
v___x_419_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v___x_418_, v_a_395_, v_snd_398_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed(lean_object* v_extFind_x3f_422_, lean_object* v_c_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(v_extFind_x3f_422_, v_c_423_, v_a_424_, v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
lean_object* v_fst_432_; lean_object* v_fst_433_; uint8_t v___x_434_; 
v_fst_432_ = lean_ctor_get(v_a_430_, 0);
v_fst_433_ = lean_ctor_get(v_b_431_, 0);
v___x_434_ = l_Lean_Name_quickLt(v_fst_432_, v_fst_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_a_435_, lean_object* v_b_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_435_, v_b_436_);
lean_dec_ref(v_b_436_);
lean_dec_ref(v_a_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(lean_object* v_as_439_, lean_object* v_k_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_m_445_; lean_object* v_a_446_; uint8_t v___x_447_; 
v___x_443_ = lean_nat_add(v_x_441_, v_x_442_);
v___x_444_ = lean_unsigned_to_nat(1u);
v_m_445_ = lean_nat_shiftr(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
v_a_446_ = lean_array_fget_borrowed(v_as_439_, v_m_445_);
v___x_447_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_446_, v_k_440_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
lean_dec(v_x_442_);
v___x_448_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_k_440_, v_a_446_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_dec(v_m_445_);
lean_dec(v_x_441_);
lean_inc(v_a_446_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_a_446_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_nat_dec_eq(v_m_445_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_nat_sub(v_m_445_, v___x_444_);
lean_dec(v_m_445_);
v___x_453_ = lean_nat_dec_lt(v___x_452_, v_x_441_);
if (v___x_453_ == 0)
{
v_x_442_ = v___x_452_;
goto _start;
}
else
{
lean_object* v___x_455_; 
lean_dec(v___x_452_);
lean_dec(v_x_441_);
v___x_455_ = lean_box(0);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_m_445_);
lean_dec(v_x_441_);
v___x_456_ = lean_box(0);
return v___x_456_;
}
}
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
lean_dec(v_x_441_);
v___x_457_ = lean_nat_add(v_m_445_, v___x_444_);
lean_dec(v_m_445_);
v___x_458_ = lean_nat_dec_le(v___x_457_, v_x_442_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v___x_457_);
lean_dec(v_x_442_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
v_x_441_ = v___x_457_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___boxed(lean_object* v_as_461_, lean_object* v_k_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_461_, v_k_462_, v_x_463_, v_x_464_);
lean_dec_ref(v_k_462_);
lean_dec_ref(v_as_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(lean_object* v_s_466_, lean_object* v_env_467_, lean_object* v_c_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_467_, v_c_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; 
lean_dec(v_c_468_);
v___x_470_ = lean_box(0);
return v___x_470_;
}
else
{
lean_object* v_val_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_val_471_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_469_, 1);
v___x_472_ = lean_array_get_size(v_s_466_);
v___x_473_ = lean_nat_dec_lt(v_val_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec(v_val_471_);
lean_dec(v_c_468_);
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_array_fget_borrowed(v_s_466_, v_val_471_);
lean_dec(v_val_471_);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_array_get_size(v___x_475_);
v___x_478_ = lean_nat_dec_lt(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec(v_c_468_);
v___x_479_ = lean_box(0);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_sub(v___x_477_, v___x_480_);
v___x_482_ = lean_nat_dec_le(v___x_476_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec(v___x_481_);
lean_dec(v_c_468_);
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0));
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_c_468_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v___x_475_, v___x_485_, v___x_476_, v___x_481_);
lean_dec_ref_known(v___x_485_, 2);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v_val_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v_val_488_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v___x_486_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_val_488_);
lean_dec(v___x_486_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_snd_492_; lean_object* v___x_494_; 
v_snd_492_ = lean_ctor_get(v_val_488_, 1);
lean_inc(v_snd_492_);
lean_dec(v_val_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_snd_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_snd_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed(lean_object* v_s_497_, lean_object* v_env_498_, lean_object* v_c_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(v_s_497_, v_env_498_, v_c_499_);
lean_dec_ref(v_env_498_);
lean_dec_ref(v_s_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(lean_object* v_as_501_, lean_object* v_k_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_501_, v_k_502_, v_x_503_, v_x_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___boxed(lean_object* v_as_507_, lean_object* v_k_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(v_as_507_, v_k_508_, v_x_509_, v_x_510_, v_x_511_);
lean_dec_ref(v_k_508_);
lean_dec_ref(v_as_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_));
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(v_x_517_);
lean_dec_ref(v_x_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object* v_x_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(v_x_521_);
lean_dec_ref(v_x_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object* v_s_523_, lean_object* v_x_524_){
_start:
{
lean_inc_ref(v_s_523_);
return v_s_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object* v_s_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(v_s_525_, v_x_526_);
lean_dec_ref(v_x_526_);
lean_dec_ref(v_s_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object* v_importedEntries_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_importedEntries_528_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object* v_importedEntries_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(v_importedEntries_532_, v___y_533_);
lean_dec_ref(v___y_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object* v_exportedEnv_536_, uint8_t v___x_537_, lean_object* v_names_538_, lean_object* v_name_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
lean_inc(v_name_539_);
v___x_541_ = l_Lean_Environment_find_x3f(v_exportedEnv_536_, v_name_539_, v___x_537_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_dec(v_name_539_);
return v_names_538_;
}
else
{
lean_object* v___x_542_; 
lean_dec_ref_known(v___x_541_, 1);
v___x_542_ = lean_array_push(v_names_538_, v_name_539_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object* v_exportedEnv_543_, lean_object* v___x_544_, lean_object* v_names_545_, lean_object* v_name_546_, lean_object* v_x_547_){
_start:
{
uint8_t v___x_1707__boxed_548_; lean_object* v_res_549_; 
v___x_1707__boxed_548_ = lean_unbox(v___x_544_);
v_res_549_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(v_exportedEnv_543_, v___x_1707__boxed_548_, v_names_545_, v_name_546_, v_x_547_);
lean_dec_ref(v_x_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_550_, lean_object* v_keys_551_, lean_object* v_vals_552_, lean_object* v_i_553_, lean_object* v_acc_554_){
_start:
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_array_get_size(v_keys_551_);
v___x_556_ = lean_nat_dec_lt(v_i_553_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v_i_553_);
lean_dec(v_f_550_);
return v_acc_554_;
}
else
{
lean_object* v_k_557_; lean_object* v_v_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_k_557_ = lean_array_fget_borrowed(v_keys_551_, v_i_553_);
v_v_558_ = lean_array_fget_borrowed(v_vals_552_, v_i_553_);
lean_inc(v_f_550_);
lean_inc(v_v_558_);
lean_inc(v_k_557_);
v___x_559_ = lean_apply_3(v_f_550_, v_acc_554_, v_k_557_, v_v_558_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_i_553_, v___x_560_);
lean_dec(v_i_553_);
v_i_553_ = v___x_561_;
v_acc_554_ = v___x_559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_563_, lean_object* v_keys_564_, lean_object* v_vals_565_, lean_object* v_i_566_, lean_object* v_acc_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_563_, v_keys_564_, v_vals_565_, v_i_566_, v_acc_567_);
lean_dec_ref(v_vals_565_);
lean_dec_ref(v_keys_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_569_, lean_object* v_as_570_, size_t v_i_571_, size_t v_stop_572_, lean_object* v_b_573_){
_start:
{
lean_object* v___y_575_; uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_eq(v_i_571_, v_stop_572_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_array_uget_borrowed(v_as_570_, v_i_571_);
switch(lean_obj_tag(v___x_580_))
{
case 0:
{
lean_object* v_key_581_; lean_object* v_val_582_; lean_object* v___x_583_; 
v_key_581_ = lean_ctor_get(v___x_580_, 0);
v_val_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_f_569_);
lean_inc(v_val_582_);
lean_inc(v_key_581_);
v___x_583_ = lean_apply_3(v_f_569_, v_b_573_, v_key_581_, v_val_582_);
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
case 1:
{
lean_object* v_node_584_; lean_object* v___x_585_; 
v_node_584_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_f_569_);
v___x_585_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_569_, v_node_584_, v_b_573_);
v___y_575_ = v___x_585_;
goto v___jp_574_;
}
default: 
{
v___y_575_ = v_b_573_;
goto v___jp_574_;
}
}
}
else
{
lean_dec(v_f_569_);
return v_b_573_;
}
v___jp_574_:
{
size_t v___x_576_; size_t v___x_577_; 
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_add(v_i_571_, v___x_576_);
v_i_571_ = v___x_577_;
v_b_573_ = v___y_575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v_es_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_es_589_ = lean_ctor_get(v_x_587_, 0);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_array_get_size(v_es_589_);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_f_586_);
return v_x_588_;
}
else
{
size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_593_ = ((size_t)0ULL);
v___x_594_ = lean_usize_of_nat(v___x_591_);
v___x_595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_586_, v_es_589_, v___x_593_, v___x_594_, v_x_588_);
return v___x_595_;
}
}
else
{
lean_object* v_ks_596_; lean_object* v_vs_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_ks_596_ = lean_ctor_get(v_x_587_, 0);
v_vs_597_ = lean_ctor_get(v_x_587_, 1);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_586_, v_ks_596_, v_vs_597_, v___x_598_, v_x_588_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_600_, v_x_601_, v_x_602_);
lean_dec_ref(v_x_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_604_, lean_object* v_as_605_, lean_object* v_i_606_, lean_object* v_stop_607_, lean_object* v_b_608_){
_start:
{
size_t v_i_boxed_609_; size_t v_stop_boxed_610_; lean_object* v_res_611_; 
v_i_boxed_609_ = lean_unbox_usize(v_i_606_);
lean_dec(v_i_606_);
v_stop_boxed_610_ = lean_unbox_usize(v_stop_607_);
lean_dec(v_stop_607_);
v_res_611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_604_, v_as_605_, v_i_boxed_609_, v_stop_boxed_610_, v_b_608_);
lean_dec_ref(v_as_605_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_612_, lean_object* v_x1_613_, lean_object* v_x2_614_, lean_object* v_x3_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_apply_3(v_f_612_, v_x1_613_, v_x2_614_, v_x3_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_617_, lean_object* v_f_618_, lean_object* v_init_619_){
_start:
{
lean_object* v___f_620_; lean_object* v___x_621_; 
v___f_620_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_620_, 0, v_f_618_);
v___x_621_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_620_, v_map_617_, v_init_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_622_, lean_object* v_f_623_, lean_object* v_init_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg(v_map_622_, v_f_623_, v_init_624_);
lean_dec_ref(v_map_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__1(lean_object* v_s_626_, size_t v_sz_627_, size_t v_i_628_, lean_object* v_bs_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = lean_usize_dec_lt(v_i_628_, v_sz_627_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec_ref(v_s_626_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_bs_629_);
lean_ctor_set(v___x_633_, 1, v___y_631_);
return v___x_633_;
}
else
{
lean_object* v_v_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_fst_637_; lean_object* v_snd_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_651_; 
v_v_634_ = lean_array_uget(v_bs_629_, v_i_628_);
lean_inc_ref(v_s_626_);
v___x_635_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed), 3, 1);
lean_closure_set(v___x_635_, 0, v_s_626_);
lean_inc(v_v_634_);
v___x_636_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(v___x_635_, v_v_634_, v___y_630_, v___y_631_);
v_fst_637_ = lean_ctor_get(v___x_636_, 0);
v_snd_638_ = lean_ctor_get(v___x_636_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_651_ == 0)
{
v___x_640_ = v___x_636_;
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_snd_638_);
lean_inc(v_fst_637_);
lean_dec(v___x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_651_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v_bs_x27_643_; lean_object* v___x_645_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v_bs_x27_643_ = lean_array_uset(v_bs_629_, v_i_628_, v___x_642_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_fst_637_);
lean_ctor_set(v___x_640_, 0, v_v_634_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_v_634_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_fst_637_);
v___x_645_ = v_reuseFailAlloc_650_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_628_, v___x_646_);
v___x_648_ = lean_array_uset(v_bs_x27_643_, v_i_628_, v___x_645_);
v_i_628_ = v___x_647_;
v_bs_629_ = v___x_648_;
v___y_631_ = v_snd_638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__1___boxed(lean_object* v_s_652_, lean_object* v_sz_653_, lean_object* v_i_654_, lean_object* v_bs_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_653_);
lean_dec(v_sz_653_);
v_i_boxed_659_ = lean_unbox_usize(v_i_654_);
lean_dec(v_i_654_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__1(v_s_652_, v_sz_boxed_658_, v_i_boxed_659_, v_bs_655_, v___y_656_, v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_661_, lean_object* v_pivot_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_k_665_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_lt(v_k_665_, v_hi_661_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_k_665_);
v___x_667_ = lean_array_fswap(v_as_663_, v_i_664_, v_hi_661_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_i_664_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v_fst_670_; lean_object* v_fst_671_; uint8_t v___x_672_; 
v___x_669_ = lean_array_fget_borrowed(v_as_663_, v_k_665_);
v_fst_670_ = lean_ctor_get(v___x_669_, 0);
v_fst_671_ = lean_ctor_get(v_pivot_662_, 0);
v___x_672_ = l_Lean_Name_quickLt(v_fst_670_, v_fst_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_k_665_, v___x_673_);
lean_dec(v_k_665_);
v_k_665_ = v___x_674_;
goto _start;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_array_fswap(v_as_663_, v_i_664_, v_k_665_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_add(v_i_664_, v___x_677_);
lean_dec(v_i_664_);
v___x_679_ = lean_nat_add(v_k_665_, v___x_677_);
lean_dec(v_k_665_);
v_as_663_ = v___x_676_;
v_i_664_ = v___x_678_;
v_k_665_ = v___x_679_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_681_, lean_object* v_pivot_682_, lean_object* v_as_683_, lean_object* v_i_684_, lean_object* v_k_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_681_, v_pivot_682_, v_as_683_, v_i_684_, v_k_685_);
lean_dec_ref(v_pivot_682_);
lean_dec(v_hi_681_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_687_, lean_object* v_as_688_, lean_object* v_lo_689_, lean_object* v_hi_690_){
_start:
{
lean_object* v___y_692_; uint8_t v___x_702_; 
v___x_702_ = lean_nat_dec_lt(v_lo_689_, v_hi_690_);
if (v___x_702_ == 0)
{
lean_dec(v_lo_689_);
return v_as_688_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_mid_705_; lean_object* v___y_707_; lean_object* v___y_713_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_703_ = lean_nat_add(v_lo_689_, v_hi_690_);
v___x_704_ = lean_unsigned_to_nat(1u);
v_mid_705_ = lean_nat_shiftr(v___x_703_, v___x_704_);
lean_dec(v___x_703_);
v___x_718_ = lean_array_fget_borrowed(v_as_688_, v_mid_705_);
v___x_719_ = lean_array_fget_borrowed(v_as_688_, v_lo_689_);
v___x_720_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
v___y_713_ = v_as_688_;
goto v___jp_712_;
}
else
{
lean_object* v___x_721_; 
v___x_721_ = lean_array_fswap(v_as_688_, v_lo_689_, v_mid_705_);
v___y_713_ = v___x_721_;
goto v___jp_712_;
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_708_ = lean_array_fget_borrowed(v___y_707_, v_mid_705_);
v___x_709_ = lean_array_fget_borrowed(v___y_707_, v_hi_690_);
v___x_710_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_708_, v___x_709_);
if (v___x_710_ == 0)
{
lean_dec(v_mid_705_);
v___y_692_ = v___y_707_;
goto v___jp_691_;
}
else
{
lean_object* v___x_711_; 
v___x_711_ = lean_array_fswap(v___y_707_, v_mid_705_, v_hi_690_);
lean_dec(v_mid_705_);
v___y_692_ = v___x_711_;
goto v___jp_691_;
}
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_array_fget_borrowed(v___y_713_, v_hi_690_);
v___x_715_ = lean_array_fget_borrowed(v___y_713_, v_lo_689_);
v___x_716_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
v___y_707_ = v___y_713_;
goto v___jp_706_;
}
else
{
lean_object* v___x_717_; 
v___x_717_ = lean_array_fswap(v___y_713_, v_lo_689_, v_hi_690_);
v___y_707_ = v___x_717_;
goto v___jp_706_;
}
}
}
v___jp_691_:
{
lean_object* v_pivot_693_; lean_object* v___x_694_; lean_object* v_fst_695_; lean_object* v_snd_696_; uint8_t v___x_697_; 
v_pivot_693_ = lean_array_fget(v___y_692_, v_hi_690_);
lean_inc_n(v_lo_689_, 2);
v___x_694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_690_, v_pivot_693_, v___y_692_, v_lo_689_, v_lo_689_);
lean_dec(v_pivot_693_);
v_fst_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_fst_695_);
v_snd_696_ = lean_ctor_get(v___x_694_, 1);
lean_inc(v_snd_696_);
lean_dec_ref(v___x_694_);
v___x_697_ = lean_nat_dec_le(v_hi_690_, v_fst_695_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg(v_n_687_, v_snd_696_, v_lo_689_, v_fst_695_);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_add(v_fst_695_, v___x_699_);
lean_dec(v_fst_695_);
v_as_688_ = v___x_698_;
v_lo_689_ = v___x_700_;
goto _start;
}
else
{
lean_dec(v_fst_695_);
lean_dec(v_lo_689_);
return v_snd_696_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_722_, lean_object* v_as_723_, lean_object* v_lo_724_, lean_object* v_hi_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg(v_n_722_, v_as_723_, v_lo_724_, v_hi_725_);
lean_dec(v_hi_725_);
lean_dec(v_n_722_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object* v___x_729_, lean_object* v_env_730_, lean_object* v_s_731_){
_start:
{
lean_object* v_checked_732_; lean_object* v___x_733_; lean_object* v_constants_734_; lean_object* v_map_u2082_735_; uint8_t v___x_736_; lean_object* v_exportedEnv_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___f_740_; lean_object* v_privateEnv_741_; lean_object* v___x_742_; lean_object* v_allNames_743_; size_t v_sz_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_entries_748_; lean_object* v___x_749_; lean_object* v___y_751_; lean_object* v___y_752_; uint8_t v___x_755_; 
v_checked_732_ = lean_ctor_get(v_env_730_, 2);
lean_inc_ref(v_checked_732_);
v___x_733_ = lean_task_get_own(v_checked_732_);
v_constants_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_ref(v_constants_734_);
lean_dec(v___x_733_);
v_map_u2082_735_ = lean_ctor_get(v_constants_734_, 1);
lean_inc_ref(v_map_u2082_735_);
lean_dec_ref(v_constants_734_);
v___x_736_ = 1;
lean_inc_ref(v_env_730_);
v_exportedEnv_737_ = l_Lean_Environment_setExporting(v_env_730_, v___x_736_);
v___x_738_ = 0;
v___x_739_ = lean_box(v___x_738_);
v___f_740_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_740_, 0, v_exportedEnv_737_);
lean_closure_set(v___f_740_, 1, v___x_739_);
v_privateEnv_741_ = l_Lean_Environment_setExporting(v_env_730_, v___x_738_);
v___x_742_ = lean_mk_empty_array_with_capacity(v___x_729_);
v_allNames_743_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg(v_map_u2082_735_, v___f_740_, v___x_742_);
lean_dec_ref(v_map_u2082_735_);
v_sz_744_ = lean_array_size(v_allNames_743_);
v___x_745_ = lean_box_usize(v_sz_744_);
v___x_746_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_));
v___x_747_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__1___boxed), 6, 4);
lean_closure_set(v___x_747_, 0, v_s_731_);
lean_closure_set(v___x_747_, 1, v___x_745_);
lean_closure_set(v___x_747_, 2, v___x_746_);
lean_closure_set(v___x_747_, 3, v_allNames_743_);
v_entries_748_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(v_privateEnv_741_, v___x_747_);
v___x_749_ = lean_array_get_size(v_entries_748_);
v___x_755_ = lean_nat_dec_eq(v___x_749_, v___x_729_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___y_759_; uint8_t v___x_761_; 
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_sub(v___x_749_, v___x_756_);
v___x_761_ = lean_nat_dec_le(v___x_729_, v___x_757_);
if (v___x_761_ == 0)
{
lean_dec(v___x_729_);
lean_inc(v___x_757_);
v___y_759_ = v___x_757_;
goto v___jp_758_;
}
else
{
v___y_759_ = v___x_729_;
goto v___jp_758_;
}
v___jp_758_:
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_le(v___y_759_, v___x_757_);
if (v___x_760_ == 0)
{
lean_dec(v___x_757_);
lean_inc(v___y_759_);
v___y_751_ = v___y_759_;
v___y_752_ = v___y_759_;
goto v___jp_750_;
}
else
{
v___y_751_ = v___y_759_;
v___y_752_ = v___x_757_;
goto v___jp_750_;
}
}
}
else
{
lean_object* v___x_762_; 
lean_dec(v___x_729_);
lean_inc_n(v_entries_748_, 2);
v___x_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_762_, 0, v_entries_748_);
lean_ctor_set(v___x_762_, 1, v_entries_748_);
lean_ctor_set(v___x_762_, 2, v_entries_748_);
return v___x_762_;
}
v___jp_750_:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg(v___x_749_, v_entries_748_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_inc_ref_n(v___x_753_, 2);
v___x_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
lean_ctor_set(v___x_754_, 2, v___x_753_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(lean_object* v___x_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object* v___x_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(v___x_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_));
v___x_818_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2____boxed(lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_();
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_821_, lean_object* v_00_u03b2_822_, lean_object* v_map_823_, lean_object* v_f_824_, lean_object* v_init_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___redArg(v_map_823_, v_f_824_, v_init_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_827_, lean_object* v_00_u03b2_828_, lean_object* v_map_829_, lean_object* v_f_830_, lean_object* v_init_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0(v_00_u03c3_827_, v_00_u03b2_828_, v_map_829_, v_f_830_, v_init_831_);
lean_dec_ref(v_map_829_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2(lean_object* v_n_833_, lean_object* v_as_834_, lean_object* v_lo_835_, lean_object* v_hi_836_, lean_object* v_w_837_, lean_object* v_hlo_838_, lean_object* v_hhi_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___redArg(v_n_833_, v_as_834_, v_lo_835_, v_hi_836_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_841_, lean_object* v_as_842_, lean_object* v_lo_843_, lean_object* v_hi_844_, lean_object* v_w_845_, lean_object* v_hlo_846_, lean_object* v_hhi_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2(v_n_841_, v_as_842_, v_lo_843_, v_hi_844_, v_w_845_, v_hlo_846_, v_hhi_847_);
lean_dec(v_hi_844_);
lean_dec(v_n_841_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_849_, lean_object* v_f_850_, lean_object* v_init_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_850_, v_map_849_, v_init_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_853_, lean_object* v_f_854_, lean_object* v_init_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_853_, v_f_854_, v_init_855_);
lean_dec_ref(v_map_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_857_, lean_object* v_00_u03b2_858_, lean_object* v_map_859_, lean_object* v_f_860_, lean_object* v_init_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_860_, v_map_859_, v_init_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_863_, lean_object* v_00_u03b2_864_, lean_object* v_map_865_, lean_object* v_f_866_, lean_object* v_init_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_863_, v_00_u03b2_864_, v_map_865_, v_f_866_, v_init_867_);
lean_dec_ref(v_map_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_869_, lean_object* v_lo_870_, lean_object* v_hi_871_, lean_object* v_hhi_872_, lean_object* v_pivot_873_, lean_object* v_as_874_, lean_object* v_i_875_, lean_object* v_k_876_, lean_object* v_ilo_877_, lean_object* v_ik_878_, lean_object* v_w_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_871_, v_pivot_873_, v_as_874_, v_i_875_, v_k_876_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_881_, lean_object* v_lo_882_, lean_object* v_hi_883_, lean_object* v_hhi_884_, lean_object* v_pivot_885_, lean_object* v_as_886_, lean_object* v_i_887_, lean_object* v_k_888_, lean_object* v_ilo_889_, lean_object* v_ik_890_, lean_object* v_w_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__2_spec__3(v_n_881_, v_lo_882_, v_hi_883_, v_hhi_884_, v_pivot_885_, v_as_886_, v_i_887_, v_k_888_, v_ilo_889_, v_ik_890_, v_w_891_);
lean_dec_ref(v_pivot_885_);
lean_dec(v_hi_883_);
lean_dec(v_lo_882_);
lean_dec(v_n_881_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_893_, lean_object* v_00_u03b1_894_, lean_object* v_00_u03b2_895_, lean_object* v_f_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_896_, v_x_897_, v_x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_900_, lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_f_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_900_, v_00_u03b1_901_, v_00_u03b2_902_, v_f_903_, v_x_904_, v_x_905_);
lean_dec_ref(v_x_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_00_u03c3_909_, lean_object* v_f_910_, lean_object* v_as_911_, size_t v_i_912_, size_t v_stop_913_, lean_object* v_b_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_910_, v_as_911_, v_i_912_, v_stop_913_, v_b_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_916_, lean_object* v_00_u03b2_917_, lean_object* v_00_u03c3_918_, lean_object* v_f_919_, lean_object* v_as_920_, lean_object* v_i_921_, lean_object* v_stop_922_, lean_object* v_b_923_){
_start:
{
size_t v_i_boxed_924_; size_t v_stop_boxed_925_; lean_object* v_res_926_; 
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_stop_boxed_925_ = lean_unbox_usize(v_stop_922_);
lean_dec(v_stop_922_);
v_res_926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b1_916_, v_00_u03b2_917_, v_00_u03c3_918_, v_f_919_, v_as_920_, v_i_boxed_924_, v_stop_boxed_925_, v_b_923_);
lean_dec_ref(v_as_920_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_927_, lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_f_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_heq_933_, lean_object* v_i_934_, lean_object* v_acc_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_930_, v_keys_931_, v_vals_932_, v_i_934_, v_acc_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_937_, lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_f_940_, lean_object* v_keys_941_, lean_object* v_vals_942_, lean_object* v_heq_943_, lean_object* v_i_944_, lean_object* v_acc_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_937_, v_00_u03b1_938_, v_00_u03b2_939_, v_f_940_, v_keys_941_, v_vals_942_, v_heq_943_, v_i_944_, v_acc_945_);
lean_dec_ref(v_vals_942_);
lean_dec_ref(v_keys_941_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object* v___x_947_, lean_object* v_constName_948_, lean_object* v_toPure_949_, lean_object* v_env_950_){
_start:
{
uint8_t v___x_951_; lean_object* v_privateEnv_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_s_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_951_ = 0;
lean_inc_ref(v_env_950_);
v_privateEnv_952_ = l_Lean_Environment_setExporting(v_env_950_, v___x_951_);
v___x_953_ = l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt;
v___x_954_ = lean_box(2);
v___x_955_ = lean_box(0);
v_s_956_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_947_, v___x_953_, v_env_950_, v___x_954_, v___x_955_, v___x_951_);
v___x_957_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed), 3, 1);
lean_closure_set(v___x_957_, 0, v_s_956_);
v___x_958_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed), 4, 2);
lean_closure_set(v___x_958_, 0, v___x_957_);
lean_closure_set(v___x_958_, 1, v_constName_948_);
v___x_959_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(v_privateEnv_952_, v___x_958_);
v___x_960_ = lean_apply_2(v_toPure_949_, lean_box(0), v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_constName_963_){
_start:
{
lean_object* v_toApplicative_964_; lean_object* v_toBind_965_; lean_object* v_getEnv_966_; lean_object* v_toPure_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___x_970_; 
v_toApplicative_964_ = lean_ctor_get(v_inst_961_, 0);
lean_inc_ref(v_toApplicative_964_);
v_toBind_965_ = lean_ctor_get(v_inst_961_, 1);
lean_inc(v_toBind_965_);
lean_dec_ref(v_inst_961_);
v_getEnv_966_ = lean_ctor_get(v_inst_962_, 0);
lean_inc(v_getEnv_966_);
lean_dec_ref(v_inst_962_);
v_toPure_967_ = lean_ctor_get(v_toApplicative_964_, 1);
lean_inc(v_toPure_967_);
lean_dec_ref(v_toApplicative_964_);
v___x_968_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState));
v___f_969_ = lean_alloc_closure((void*)(l_Lean_collectAxioms___redArg___lam__0), 4, 3);
lean_closure_set(v___f_969_, 0, v___x_968_);
lean_closure_set(v___f_969_, 1, v_constName_963_);
lean_closure_set(v___f_969_, 2, v_toPure_967_);
v___x_970_ = lean_apply_4(v_toBind_965_, lean_box(0), lean_box(0), v_getEnv_966_, v___f_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object* v_m_971_, lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_constName_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_collectAxioms___redArg(v_inst_972_, v_inst_973_, v_constName_974_);
return v___x_975_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectAxioms(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_53144371____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectAxioms(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectAxioms(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectAxioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectAxioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectAxioms(builtin);
}
#ifdef __cplusplus
}
#endif
