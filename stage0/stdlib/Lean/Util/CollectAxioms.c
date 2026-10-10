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
static const lean_array_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 20, 155, 62, 160, 30, 19, 156)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "CollectAxioms"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 55, 253, 35, 47, 204, 39, 222)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(110, 123, 114, 100, 179, 32, 115, 58)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 81, 169, 218, 186, 106, 123, 199)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "exportedAxiomsExt"};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 165, 200, 187, 116, 224, 61, 196)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value)} };
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 8, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(lean_object* v_as_13_, size_t v_i_14_, size_t v_stop_15_, lean_object* v_b_16_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_13_ = stack[0].m_obj;
size_t v_i_14_ = stack[1].m_num;
size_t v_stop_15_ = stack[2].m_num;
lean_object* v_b_16_ = stack[3].m_obj;
lean_object* v_res_23_;
v_res_23_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_as_13_, v_i_14_, v_stop_15_, v_b_16_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0___boxed(lean_object* v_as_24_, lean_object* v_i_25_, lean_object* v_stop_26_, lean_object* v_b_27_){
_start:
{
size_t v_i_boxed_28_; size_t v_stop_boxed_29_; lean_object* v_res_30_; 
v_i_boxed_28_ = lean_unbox_usize(v_i_25_);
lean_dec(v_i_25_);
v_stop_boxed_29_ = lean_unbox_usize(v_stop_26_);
lean_dec(v_stop_26_);
v_res_30_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_as_24_, v_i_boxed_28_, v_stop_boxed_29_, v_b_27_);
lean_dec_ref(v_as_24_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(lean_object* v_s_31_, lean_object* v_axs_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_array_get_size(v_axs_32_);
v___x_35_ = lean_nat_dec_lt(v___x_33_, v___x_34_);
if (v___x_35_ == 0)
{
return v_s_31_;
}
else
{
uint8_t v___x_36_; 
v___x_36_ = lean_nat_dec_le(v___x_34_, v___x_34_);
if (v___x_36_ == 0)
{
if (v___x_35_ == 0)
{
return v_s_31_;
}
else
{
size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((size_t)0ULL);
v___x_38_ = lean_usize_of_nat(v___x_34_);
v___x_39_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_32_, v___x_37_, v___x_38_, v_s_31_);
return v___x_39_;
}
}
else
{
size_t v___x_40_; size_t v___x_41_; lean_object* v___x_42_; 
v___x_40_ = ((size_t)0ULL);
v___x_41_ = lean_usize_of_nat(v___x_34_);
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_32_, v___x_40_, v___x_41_, v_s_31_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray___boxed(lean_object* v_s_43_, lean_object* v_axs_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_s_43_, v_axs_44_);
lean_dec_ref(v_axs_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(lean_object* v_init_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 0)
{
lean_object* v_k_48_; lean_object* v_l_49_; lean_object* v_r_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_k_48_ = lean_ctor_get(v_x_47_, 1);
lean_inc(v_k_48_);
v_l_49_ = lean_ctor_get(v_x_47_, 3);
lean_inc(v_l_49_);
v_r_50_ = lean_ctor_get(v_x_47_, 4);
lean_inc(v_r_50_);
lean_dec_ref_known(v_x_47_, 5);
v___x_51_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_46_, v_l_49_);
v___x_52_ = lean_array_push(v___x_51_, v_k_48_);
v_init_46_ = v___x_52_;
v_x_47_ = v_r_50_;
goto _start;
}
else
{
return v_init_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(lean_object* v_hi_54_, lean_object* v_pivot_55_, lean_object* v_as_56_, lean_object* v_i_57_, lean_object* v_k_58_){
_start:
{
uint8_t v___x_59_; 
v___x_59_ = lean_nat_dec_lt(v_k_58_, v_hi_54_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec(v_k_58_);
v___x_60_ = lean_array_fswap(v_as_56_, v_i_57_, v_hi_54_);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v_i_57_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_array_fget_borrowed(v_as_56_, v_k_58_);
v___x_63_ = l_Lean_Name_lt(v___x_62_, v_pivot_55_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_k_58_, v___x_64_);
lean_dec(v_k_58_);
v_k_58_ = v___x_65_;
goto _start;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = lean_array_fswap(v_as_56_, v_i_57_, v_k_58_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = lean_nat_add(v_i_57_, v___x_68_);
lean_dec(v_i_57_);
v___x_70_ = lean_nat_add(v_k_58_, v___x_68_);
lean_dec(v_k_58_);
v_as_56_ = v___x_67_;
v_i_57_ = v___x_69_;
v_k_58_ = v___x_70_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg___boxed(lean_object* v_hi_72_, lean_object* v_pivot_73_, lean_object* v_as_74_, lean_object* v_i_75_, lean_object* v_k_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_72_, v_pivot_73_, v_as_74_, v_i_75_, v_k_76_);
lean_dec(v_pivot_73_);
lean_dec(v_hi_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(lean_object* v_n_78_, lean_object* v_as_79_, lean_object* v_lo_80_, lean_object* v_hi_81_){
_start:
{
lean_object* v___y_83_; uint8_t v___x_93_; 
v___x_93_ = lean_nat_dec_lt(v_lo_80_, v_hi_81_);
if (v___x_93_ == 0)
{
lean_dec(v_lo_80_);
return v_as_79_;
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_mid_96_; lean_object* v___y_98_; lean_object* v___y_104_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_94_ = lean_nat_add(v_lo_80_, v_hi_81_);
v___x_95_ = lean_unsigned_to_nat(1u);
v_mid_96_ = lean_nat_shiftr(v___x_94_, v___x_95_);
lean_dec(v___x_94_);
v___x_109_ = lean_array_fget_borrowed(v_as_79_, v_mid_96_);
v___x_110_ = lean_array_fget_borrowed(v_as_79_, v_lo_80_);
v___x_111_ = l_Lean_Name_lt(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
v___y_104_ = v_as_79_;
goto v___jp_103_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_array_fswap(v_as_79_, v_lo_80_, v_mid_96_);
v___y_104_ = v___x_112_;
goto v___jp_103_;
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = lean_array_fget_borrowed(v___y_98_, v_mid_96_);
v___x_100_ = lean_array_fget_borrowed(v___y_98_, v_hi_81_);
v___x_101_ = l_Lean_Name_lt(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_dec(v_mid_96_);
v___y_83_ = v___y_98_;
goto v___jp_82_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_array_fswap(v___y_98_, v_mid_96_, v_hi_81_);
lean_dec(v_mid_96_);
v___y_83_ = v___x_102_;
goto v___jp_82_;
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = lean_array_fget_borrowed(v___y_104_, v_hi_81_);
v___x_106_ = lean_array_fget_borrowed(v___y_104_, v_lo_80_);
v___x_107_ = l_Lean_Name_lt(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
v___y_98_ = v___y_104_;
goto v___jp_97_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_array_fswap(v___y_104_, v_lo_80_, v_hi_81_);
v___y_98_ = v___x_108_;
goto v___jp_97_;
}
}
}
v___jp_82_:
{
lean_object* v_pivot_84_; lean_object* v___x_85_; lean_object* v_fst_86_; lean_object* v_snd_87_; uint8_t v___x_88_; 
v_pivot_84_ = lean_array_fget(v___y_83_, v_hi_81_);
lean_inc_n(v_lo_80_, 2);
v___x_85_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_81_, v_pivot_84_, v___y_83_, v_lo_80_, v_lo_80_);
lean_dec(v_pivot_84_);
v_fst_86_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_fst_86_);
v_snd_87_ = lean_ctor_get(v___x_85_, 1);
lean_inc(v_snd_87_);
lean_dec_ref(v___x_85_);
v___x_88_ = lean_nat_dec_le(v_hi_81_, v_fst_86_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_78_, v_snd_87_, v_lo_80_, v_fst_86_);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_add(v_fst_86_, v___x_90_);
lean_dec(v_fst_86_);
v_as_79_ = v___x_89_;
v_lo_80_ = v___x_91_;
goto _start;
}
else
{
lean_dec(v_fst_86_);
lean_dec(v_lo_80_);
return v_snd_87_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg___boxed(lean_object* v_n_113_, lean_object* v_as_114_, lean_object* v_lo_115_, lean_object* v_hi_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_113_, v_as_114_, v_lo_115_, v_hi_116_);
lean_dec(v_hi_116_);
lean_dec(v_n_113_);
return v_res_117_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(lean_object* v_extFind_x3f_120_, lean_object* v_as_121_, size_t v_i_122_, size_t v_stop_123_, lean_object* v_b_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_usize_dec_eq(v_i_122_, v_stop_123_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v_fst_130_; lean_object* v_snd_131_; size_t v___x_132_; size_t v___x_133_; 
v___x_128_ = lean_array_uget_borrowed(v_as_121_, v_i_122_);
lean_inc(v___x_128_);
lean_inc_ref(v_extFind_x3f_120_);
v___x_129_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_120_, v___x_128_, v___y_125_, v___y_126_);
v_fst_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_fst_130_);
v_snd_131_ = lean_ctor_get(v___x_129_, 1);
lean_inc(v_snd_131_);
lean_dec_ref(v___x_129_);
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_add(v_i_122_, v___x_132_);
v_i_122_ = v___x_133_;
v_b_124_ = v_fst_130_;
v___y_126_ = v_snd_131_;
goto _start;
}
else
{
lean_object* v___x_135_; 
lean_dec_ref(v_extFind_x3f_120_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v_b_124_);
lean_ctor_set(v___x_135_, 1, v___y_126_);
return v___x_135_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_extFind_x3f_120_ = stack[0].m_obj;
lean_object* v_as_121_ = stack[1].m_obj;
size_t v_i_122_ = stack[2].m_num;
size_t v_stop_123_ = stack[3].m_num;
lean_object* v_b_124_ = stack[4].m_obj;
lean_object* v___y_125_ = stack[5].m_obj;
lean_object* v___y_126_ = stack[6].m_obj;
lean_object* v_res_136_;
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_120_, v_as_121_, v_i_122_, v_stop_123_, v_b_124_, v___y_125_, v___y_126_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(lean_object* v_extFind_x3f_137_, lean_object* v_e_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = l_Lean_Expr_getUsedConstants(v_e_138_);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_get_size(v___x_141_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_nat_dec_lt(v___x_142_, v___x_143_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
lean_dec_ref(v___x_141_);
lean_dec_ref(v_extFind_x3f_137_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___y_140_);
return v___x_146_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = lean_nat_dec_le(v___x_143_, v___x_143_);
if (v___x_147_ == 0)
{
if (v___x_145_ == 0)
{
lean_object* v___x_148_; 
lean_dec_ref(v___x_141_);
lean_dec_ref(v_extFind_x3f_137_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_144_);
lean_ctor_set(v___x_148_, 1, v___y_140_);
return v___x_148_;
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_143_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_137_, v___x_141_, v___x_149_, v___x_150_, v___x_144_, v___y_139_, v___y_140_);
lean_dec_ref(v___x_141_);
return v___x_151_;
}
}
else
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; 
v___x_152_ = ((size_t)0ULL);
v___x_153_ = lean_usize_of_nat(v___x_143_);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_137_, v___x_141_, v___x_152_, v___x_153_, v___x_144_, v___y_139_, v___y_140_);
lean_dec_ref(v___x_141_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(lean_object* v_extFind_x3f_155_, lean_object* v_c_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; 
lean_inc_ref(v_extFind_x3f_155_);
lean_inc(v_c_156_);
lean_inc_ref(v_a_157_);
v___x_159_ = lean_apply_2(v_extFind_x3f_155_, v_a_157_, v_c_156_);
if (lean_obj_tag(v___x_159_) == 1)
{
lean_object* v_val_160_; lean_object* v_seen_161_; lean_object* v_axioms_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_173_; 
lean_dec_ref(v_extFind_x3f_155_);
v_val_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v___x_159_, 1);
v_seen_161_ = lean_ctor_get(v_a_158_, 0);
v_axioms_162_ = lean_ctor_get(v_a_158_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_a_158_);
if (v_isSharedCheck_173_ == 0)
{
v___x_164_ = v_a_158_;
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_axioms_162_);
lean_inc(v_seen_161_);
lean_dec(v_a_158_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
lean_inc(v_val_160_);
v___x_166_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_156_, v_val_160_, v_seen_161_);
v___x_167_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_axioms_162_, v_val_160_);
lean_dec(v_val_160_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v___x_167_);
lean_ctor_set(v___x_164_, 0, v___x_166_);
v___x_169_ = v___x_164_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_167_);
v___x_169_ = v_reuseFailAlloc_172_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_box(0);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
return v___x_171_;
}
}
}
else
{
lean_object* v_seen_174_; lean_object* v_axioms_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_280_; 
lean_dec(v___x_159_);
v_seen_174_ = lean_ctor_get(v_a_158_, 0);
v_axioms_175_ = lean_ctor_get(v_a_158_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_a_158_);
if (v_isSharedCheck_280_ == 0)
{
v___x_177_ = v_a_158_;
v_isShared_178_ = v_isSharedCheck_280_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_axioms_175_);
lean_inc(v_seen_174_);
lean_dec(v_a_158_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_280_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___y_180_; lean_object* v___y_181_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_222_; lean_object* v_axioms_223_; lean_object* v___y_227_; lean_object* v___x_229_; 
v___x_229_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_174_, v_c_156_);
if (lean_obj_tag(v___x_229_) == 1)
{
lean_object* v_val_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_c_156_);
lean_dec_ref(v_extFind_x3f_155_);
v_val_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_229_, 1);
v___x_231_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_axioms_175_, v_val_230_);
lean_dec(v_val_230_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_231_);
v___x_233_ = v___x_177_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_seen_174_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_236_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
return v___x_235_;
}
}
else
{
lean_object* v_checked_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
lean_dec(v___x_229_);
v_checked_237_ = lean_ctor_get(v_a_157_, 2);
v___x_238_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0));
lean_inc(v_c_156_);
v___x_239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_156_, v___x_238_, v_seen_174_);
v___x_240_ = l_Lean_NameSet_empty;
lean_inc(v___x_239_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_240_);
lean_ctor_set(v___x_177_, 0, v___x_239_);
v___x_242_ = v___x_177_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_279_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_inc_ref(v_checked_237_);
v___x_243_ = lean_task_get_own(v_checked_237_);
lean_inc(v_c_156_);
v___x_244_ = lean_environment_find(v___x_243_, v_c_156_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_dec(v___x_239_);
lean_dec_ref(v_extFind_x3f_155_);
v___y_222_ = v___x_242_;
v_axioms_223_ = v___x_240_;
goto v___jp_221_;
}
else
{
lean_object* v_val_245_; 
v_val_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v___x_244_, 1);
switch(lean_obj_tag(v_val_245_))
{
case 0:
{
lean_object* v_val_246_; lean_object* v_toConstantVal_247_; lean_object* v_type_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_snd_252_; 
lean_dec_ref(v___x_242_);
v_val_246_ = lean_ctor_get(v_val_245_, 0);
lean_inc_ref(v_val_246_);
lean_dec_ref_known(v_val_245_, 1);
v_toConstantVal_247_ = lean_ctor_get(v_val_246_, 0);
lean_inc_ref(v_toConstantVal_247_);
lean_dec_ref(v_val_246_);
v_type_248_ = lean_ctor_get(v_toConstantVal_247_, 2);
lean_inc_ref(v_type_248_);
lean_dec_ref(v_toConstantVal_247_);
lean_inc(v_c_156_);
v___x_249_ = l_Lean_NameSet_insert(v___x_240_, v_c_156_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_239_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_155_, v_type_248_, v_a_157_, v___x_250_);
v_snd_252_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_snd_252_);
lean_dec_ref(v___x_251_);
v___y_227_ = v_snd_252_;
goto v___jp_226_;
}
case 4:
{
lean_dec_ref_known(v_val_245_, 1);
lean_dec(v___x_239_);
lean_dec_ref(v_extFind_x3f_155_);
v___y_222_ = v___x_242_;
v_axioms_223_ = v___x_240_;
goto v___jp_221_;
}
case 5:
{
lean_object* v_val_253_; lean_object* v_toConstantVal_254_; lean_object* v_ctors_255_; lean_object* v_type_256_; lean_object* v___x_257_; lean_object* v_snd_258_; lean_object* v___x_259_; lean_object* v_snd_260_; 
lean_dec(v___x_239_);
v_val_253_ = lean_ctor_get(v_val_245_, 0);
lean_inc_ref(v_val_253_);
lean_dec_ref_known(v_val_245_, 1);
v_toConstantVal_254_ = lean_ctor_get(v_val_253_, 0);
lean_inc_ref(v_toConstantVal_254_);
v_ctors_255_ = lean_ctor_get(v_val_253_, 4);
lean_inc(v_ctors_255_);
lean_dec_ref(v_val_253_);
v_type_256_ = lean_ctor_get(v_toConstantVal_254_, 2);
lean_inc_ref(v_type_256_);
lean_dec_ref(v_toConstantVal_254_);
lean_inc_ref(v_extFind_x3f_155_);
v___x_257_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_155_, v_type_256_, v_a_157_, v___x_242_);
v_snd_258_ = lean_ctor_get(v___x_257_, 1);
lean_inc(v_snd_258_);
lean_dec_ref(v___x_257_);
v___x_259_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_155_, v_ctors_255_, v_a_157_, v_snd_258_);
v_snd_260_ = lean_ctor_get(v___x_259_, 1);
lean_inc(v_snd_260_);
lean_dec_ref(v___x_259_);
v___y_227_ = v_snd_260_;
goto v___jp_226_;
}
case 6:
{
lean_object* v_val_261_; lean_object* v_toConstantVal_262_; lean_object* v_type_263_; lean_object* v___x_264_; lean_object* v_snd_265_; 
lean_dec(v___x_239_);
v_val_261_ = lean_ctor_get(v_val_245_, 0);
lean_inc_ref(v_val_261_);
lean_dec_ref_known(v_val_245_, 1);
v_toConstantVal_262_ = lean_ctor_get(v_val_261_, 0);
lean_inc_ref(v_toConstantVal_262_);
lean_dec_ref(v_val_261_);
v_type_263_ = lean_ctor_get(v_toConstantVal_262_, 2);
lean_inc_ref(v_type_263_);
lean_dec_ref(v_toConstantVal_262_);
v___x_264_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_155_, v_type_263_, v_a_157_, v___x_242_);
v_snd_265_ = lean_ctor_get(v___x_264_, 1);
lean_inc(v_snd_265_);
lean_dec_ref(v___x_264_);
v___y_227_ = v_snd_265_;
goto v___jp_226_;
}
case 7:
{
lean_object* v_val_266_; lean_object* v_toConstantVal_267_; lean_object* v_type_268_; lean_object* v___x_269_; lean_object* v_snd_270_; 
lean_dec(v___x_239_);
v_val_266_ = lean_ctor_get(v_val_245_, 0);
lean_inc_ref(v_val_266_);
lean_dec_ref_known(v_val_245_, 1);
v_toConstantVal_267_ = lean_ctor_get(v_val_266_, 0);
lean_inc_ref(v_toConstantVal_267_);
lean_dec_ref(v_val_266_);
v_type_268_ = lean_ctor_get(v_toConstantVal_267_, 2);
lean_inc_ref(v_type_268_);
lean_dec_ref(v_toConstantVal_267_);
v___x_269_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_155_, v_type_268_, v_a_157_, v___x_242_);
v_snd_270_ = lean_ctor_get(v___x_269_, 1);
lean_inc(v_snd_270_);
lean_dec_ref(v___x_269_);
v___y_227_ = v_snd_270_;
goto v___jp_226_;
}
default: 
{
lean_object* v_val_271_; lean_object* v_toConstantVal_272_; lean_object* v_value_273_; lean_object* v_type_274_; lean_object* v___x_275_; lean_object* v_snd_276_; lean_object* v___x_277_; lean_object* v_snd_278_; 
lean_dec(v___x_239_);
v_val_271_ = lean_ctor_get(v_val_245_, 0);
lean_inc_ref(v_val_271_);
lean_dec(v_val_245_);
v_toConstantVal_272_ = lean_ctor_get(v_val_271_, 0);
lean_inc_ref(v_toConstantVal_272_);
v_value_273_ = lean_ctor_get(v_val_271_, 1);
lean_inc_ref(v_value_273_);
lean_dec_ref(v_val_271_);
v_type_274_ = lean_ctor_get(v_toConstantVal_272_, 2);
lean_inc_ref(v_type_274_);
lean_dec_ref(v_toConstantVal_272_);
lean_inc_ref(v_extFind_x3f_155_);
v___x_275_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_155_, v_type_274_, v_a_157_, v___x_242_);
v_snd_276_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_snd_276_);
lean_dec_ref(v___x_275_);
v___x_277_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_155_, v_value_273_, v_a_157_, v_snd_276_);
v_snd_278_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_snd_278_);
lean_dec_ref(v___x_277_);
v___y_227_ = v_snd_278_;
goto v___jp_226_;
}
}
}
}
}
v___jp_179_:
{
lean_object* v_seen_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_193_; 
v_seen_182_ = lean_ctor_get(v___y_180_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___y_180_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v___y_180_, 1);
lean_dec(v_unused_194_);
v___x_184_ = v___y_180_;
v_isShared_185_ = v_isSharedCheck_193_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_seen_182_);
lean_dec(v___y_180_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_193_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_186_ = lean_box(0);
lean_inc_ref(v___y_181_);
v___x_187_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_156_, v___y_181_, v_seen_182_);
v___x_188_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(v_axioms_175_, v___y_181_);
lean_dec_ref(v___y_181_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___x_188_);
lean_ctor_set(v___x_184_, 0, v___x_187_);
v___x_190_ = v___x_184_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_186_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
return v___x_191_;
}
}
}
v___jp_195_:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v___y_197_, v___y_199_, v___y_196_, v___y_200_);
lean_dec(v___y_200_);
lean_dec(v___y_197_);
v___y_180_ = v___y_198_;
v___y_181_ = v___x_201_;
goto v___jp_179_;
}
v___jp_202_:
{
uint8_t v___x_208_; 
v___x_208_ = lean_nat_dec_le(v___y_207_, v___y_203_);
if (v___x_208_ == 0)
{
lean_dec(v___y_203_);
lean_inc(v___y_207_);
v___y_196_ = v___y_207_;
v___y_197_ = v___y_204_;
v___y_198_ = v___y_205_;
v___y_199_ = v___y_206_;
v___y_200_ = v___y_207_;
goto v___jp_195_;
}
else
{
v___y_196_ = v___y_207_;
v___y_197_ = v___y_204_;
v___y_198_ = v___y_205_;
v___y_199_ = v___y_206_;
v___y_200_ = v___y_203_;
goto v___jp_195_;
}
}
v___jp_209_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_213_ = lean_mk_empty_array_with_capacity(v___y_212_);
lean_dec(v___y_212_);
v___x_214_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v___x_213_, v___y_210_);
v___x_215_ = lean_array_get_size(v___x_214_);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_nat_dec_eq(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_sub(v___x_215_, v___x_218_);
v___x_220_ = lean_nat_dec_le(v___x_216_, v___x_219_);
if (v___x_220_ == 0)
{
lean_inc(v___x_219_);
v___y_203_ = v___x_219_;
v___y_204_ = v___x_215_;
v___y_205_ = v___y_211_;
v___y_206_ = v___x_214_;
v___y_207_ = v___x_219_;
goto v___jp_202_;
}
else
{
v___y_203_ = v___x_219_;
v___y_204_ = v___x_215_;
v___y_205_ = v___y_211_;
v___y_206_ = v___x_214_;
v___y_207_ = v___x_216_;
goto v___jp_202_;
}
}
else
{
v___y_180_ = v___y_211_;
v___y_181_ = v___x_214_;
goto v___jp_179_;
}
}
v___jp_221_:
{
if (lean_obj_tag(v_axioms_223_) == 0)
{
lean_object* v_size_224_; 
v_size_224_ = lean_ctor_get(v_axioms_223_, 0);
lean_inc(v_size_224_);
v___y_210_ = v_axioms_223_;
v___y_211_ = v___y_222_;
v___y_212_ = v_size_224_;
goto v___jp_209_;
}
else
{
lean_object* v___x_225_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___y_210_ = v_axioms_223_;
v___y_211_ = v___y_222_;
v___y_212_ = v___x_225_;
goto v___jp_209_;
}
}
v___jp_226_:
{
lean_object* v_axioms_228_; 
v_axioms_228_ = lean_ctor_get(v___y_227_, 1);
lean_inc(v_axioms_228_);
v___y_222_ = v___y_227_;
v_axioms_223_ = v_axioms_228_;
goto v___jp_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(lean_object* v_extFind_x3f_281_, lean_object* v_as_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
if (lean_obj_tag(v_as_282_) == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v_extFind_x3f_281_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___y_284_);
return v___x_286_;
}
else
{
lean_object* v_head_287_; lean_object* v_tail_288_; lean_object* v___x_289_; lean_object* v_snd_290_; 
v_head_287_ = lean_ctor_get(v_as_282_, 0);
lean_inc(v_head_287_);
v_tail_288_ = lean_ctor_get(v_as_282_, 1);
lean_inc(v_tail_288_);
lean_dec_ref_known(v_as_282_, 2);
lean_inc_ref(v_extFind_x3f_281_);
v___x_289_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_281_, v_head_287_, v___y_283_, v___y_284_);
v_snd_290_ = lean_ctor_get(v___x_289_, 1);
lean_inc(v_snd_290_);
lean_dec_ref(v___x_289_);
v_as_282_ = v_tail_288_;
v___y_284_ = v_snd_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3___boxed(lean_object* v_extFind_x3f_292_, lean_object* v_as_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_292_, v_as_293_, v___y_294_, v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0___boxed(lean_object* v_extFind_x3f_297_, lean_object* v_as_298_, lean_object* v_i_299_, lean_object* v_stop_300_, lean_object* v_b_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
size_t v_i_boxed_304_; size_t v_stop_boxed_305_; lean_object* v_res_306_; 
v_i_boxed_304_ = lean_unbox_usize(v_i_299_);
lean_dec(v_i_299_);
v_stop_boxed_305_ = lean_unbox_usize(v_stop_300_);
lean_dec(v_stop_300_);
v_res_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_297_, v_as_298_, v_i_boxed_304_, v_stop_boxed_305_, v_b_301_, v___y_302_, v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec_ref(v_as_298_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0___boxed(lean_object* v_extFind_x3f_307_, lean_object* v_e_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_307_, v_e_308_, v___y_309_, v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___boxed(lean_object* v_extFind_x3f_312_, lean_object* v_c_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_312_, v_c_313_, v_a_314_, v_a_315_);
lean_dec_ref(v_a_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1(lean_object* v_init_317_, lean_object* v_t_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_317_, v_t_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(lean_object* v_n_320_, lean_object* v_as_321_, lean_object* v_lo_322_, lean_object* v_hi_323_, lean_object* v_w_324_, lean_object* v_hlo_325_, lean_object* v_hhi_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_320_, v_as_321_, v_lo_322_, v_hi_323_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___boxed(lean_object* v_n_328_, lean_object* v_as_329_, lean_object* v_lo_330_, lean_object* v_hi_331_, lean_object* v_w_332_, lean_object* v_hlo_333_, lean_object* v_hhi_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(v_n_328_, v_as_329_, v_lo_330_, v_hi_331_, v_w_332_, v_hlo_333_, v_hhi_334_);
lean_dec(v_hi_331_);
lean_dec(v_n_328_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(lean_object* v_n_336_, lean_object* v_lo_337_, lean_object* v_hi_338_, lean_object* v_hhi_339_, lean_object* v_pivot_340_, lean_object* v_as_341_, lean_object* v_i_342_, lean_object* v_k_343_, lean_object* v_ilo_344_, lean_object* v_ik_345_, lean_object* v_w_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_338_, v_pivot_340_, v_as_341_, v_i_342_, v_k_343_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___boxed(lean_object* v_n_348_, lean_object* v_lo_349_, lean_object* v_hi_350_, lean_object* v_hhi_351_, lean_object* v_pivot_352_, lean_object* v_as_353_, lean_object* v_i_354_, lean_object* v_k_355_, lean_object* v_ilo_356_, lean_object* v_ik_357_, lean_object* v_w_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(v_n_348_, v_lo_349_, v_hi_350_, v_hhi_351_, v_pivot_352_, v_as_353_, v_i_354_, v_k_355_, v_ilo_356_, v_ik_357_, v_w_358_);
lean_dec(v_pivot_352_);
lean_dec(v_hi_350_);
lean_dec(v_lo_349_);
lean_dec(v_n_348_);
return v_res_359_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Array_instInhabited___redArg();
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(lean_object* v_msg_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___f_371_; lean_object* v___f_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___f_381_; lean_object* v___f_382_; lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___x_981__overap_394_; lean_object* v___x_395_; 
v___f_371_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0));
v___f_372_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1));
v___f_373_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2));
v___f_374_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3));
v___f_375_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4));
v___f_376_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5));
v___f_377_ = ((lean_object*)(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6));
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___f_371_);
lean_ctor_set(v___x_378_, 1, v___f_372_);
v___x_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___f_373_);
lean_ctor_set(v___x_379_, 2, v___f_374_);
lean_ctor_set(v___x_379_, 3, v___f_375_);
lean_ctor_set(v___x_379_, 4, v___f_376_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___f_377_);
lean_inc_ref_n(v___x_380_, 6);
v___f_381_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_381_, 0, v___x_380_);
v___f_382_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_382_, 0, v___x_380_);
v___f_383_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_383_, 0, v___x_380_);
v___f_384_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_384_, 0, v___x_380_);
v___x_385_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_385_, 0, lean_box(0));
lean_closure_set(v___x_385_, 1, lean_box(0));
lean_closure_set(v___x_385_, 2, v___x_380_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___f_381_);
v___x_387_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_387_, 0, lean_box(0));
lean_closure_set(v___x_387_, 1, lean_box(0));
lean_closure_set(v___x_387_, 2, v___x_380_);
v___x_388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
lean_ctor_set(v___x_388_, 2, v___f_382_);
lean_ctor_set(v___x_388_, 3, v___f_383_);
lean_ctor_set(v___x_388_, 4, v___f_384_);
v___x_389_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_389_, 0, lean_box(0));
lean_closure_set(v___x_389_, 1, lean_box(0));
lean_closure_set(v___x_389_, 2, v___x_380_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_obj_once(&l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7, &l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once, _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7);
v___x_392_ = l_instInhabitedOfMonad___redArg(v___x_390_, v___x_391_);
v___f_393_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_393_, 0, v___x_392_);
v___x_981__overap_394_ = lean_panic_fn_borrowed(v___f_393_, v_msg_368_);
lean_dec_ref(v___f_393_);
lean_inc_ref(v___y_369_);
v___x_395_ = lean_apply_2(v___x_981__overap_394_, v___y_369_, v___y_370_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___boxed(lean_object* v_msg_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v_msg_396_, v___y_397_, v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(lean_object* v_extFind_x3f_404_, lean_object* v_c_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; lean_object* v_snd_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_431_; 
lean_inc(v_c_405_);
v___x_408_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(v_extFind_x3f_404_, v_c_405_, v_a_406_, v_a_407_);
v_snd_409_ = lean_ctor_get(v___x_408_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v___x_408_, 0);
lean_dec(v_unused_432_);
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_431_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_snd_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_431_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_seen_413_; lean_object* v___x_414_; 
v_seen_413_ = lean_ctor_get(v_snd_409_, 0);
v___x_414_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_413_, v_c_405_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_val_415_; lean_object* v___x_417_; 
lean_dec(v_c_405_);
v_val_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v___x_414_, 1);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v_val_415_);
v___x_417_ = v___x_411_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_val_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_snd_409_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v___x_414_);
lean_del_object(v___x_411_);
v___x_419_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0));
v___x_420_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1));
v___x_421_ = lean_unsigned_to_nat(81u);
v___x_422_ = lean_unsigned_to_nat(41u);
v___x_423_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2));
v___x_424_ = 1;
v___x_425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_405_, v___x_424_);
v___x_426_ = lean_string_append(v___x_423_, v___x_425_);
lean_dec_ref(v___x_425_);
v___x_427_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3));
v___x_428_ = lean_string_append(v___x_426_, v___x_427_);
v___x_429_ = l_mkPanicMessageWithDecl(v___x_419_, v___x_420_, v___x_421_, v___x_422_, v___x_428_);
lean_dec_ref(v___x_428_);
v___x_430_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v___x_429_, v_a_406_, v_snd_409_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed(lean_object* v_extFind_x3f_433_, lean_object* v_c_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(v_extFind_x3f_433_, v_c_434_, v_a_435_, v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_437_;
}
}
uint8_t l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(lean_object* v_a_441_, lean_object* v_b_442_){
_start:
{
lean_object* v_fst_443_; lean_object* v_fst_444_; uint8_t v___x_445_; 
v_fst_443_ = lean_ctor_get(v_a_441_, 0);
v_fst_444_ = lean_ctor_get(v_b_442_, 0);
v___x_445_ = l_Lean_Name_quickLt(v_fst_443_, v_fst_444_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_441_ = stack[0].m_obj;
lean_object* v_b_442_ = stack[1].m_obj;
uint8_t v_res_446_;
v_res_446_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_441_, v_b_442_);
stack->m_num = v_res_446_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_447_, v_b_448_);
lean_dec_ref(v_b_448_);
lean_dec_ref(v_a_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(lean_object* v_as_451_, lean_object* v_k_452_, lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_m_457_; lean_object* v_a_458_; uint8_t v___x_459_; 
v___x_455_ = lean_nat_add(v_x_453_, v_x_454_);
v___x_456_ = lean_unsigned_to_nat(1u);
v_m_457_ = lean_nat_shiftr(v___x_455_, v___x_456_);
lean_dec(v___x_455_);
v_a_458_ = lean_array_fget_borrowed(v_as_451_, v_m_457_);
v___x_459_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_458_, v_k_452_);
if (v___x_459_ == 0)
{
uint8_t v___x_460_; 
lean_dec(v_x_454_);
v___x_460_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_k_452_, v_a_458_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v_m_457_);
lean_dec(v_x_453_);
lean_inc(v_a_458_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_a_458_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_nat_dec_eq(v_m_457_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_nat_sub(v_m_457_, v___x_456_);
lean_dec(v_m_457_);
v___x_465_ = lean_nat_dec_lt(v___x_464_, v_x_453_);
if (v___x_465_ == 0)
{
v_x_454_ = v___x_464_;
goto _start;
}
else
{
lean_object* v___x_467_; 
lean_dec(v___x_464_);
lean_dec(v_x_453_);
v___x_467_ = lean_box(0);
return v___x_467_;
}
}
else
{
lean_object* v___x_468_; 
lean_dec(v_m_457_);
lean_dec(v_x_453_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
}
}
else
{
lean_object* v___x_469_; uint8_t v___x_470_; 
lean_dec(v_x_453_);
v___x_469_ = lean_nat_add(v_m_457_, v___x_456_);
lean_dec(v_m_457_);
v___x_470_ = lean_nat_dec_le(v___x_469_, v_x_454_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_dec(v___x_469_);
lean_dec(v_x_454_);
v___x_471_ = lean_box(0);
return v___x_471_;
}
else
{
v_x_453_ = v___x_469_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___boxed(lean_object* v_as_473_, lean_object* v_k_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_473_, v_k_474_, v_x_475_, v_x_476_);
lean_dec_ref(v_k_474_);
lean_dec_ref(v_as_473_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(lean_object* v_s_478_, lean_object* v_env_479_, lean_object* v_c_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_479_, v_c_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v___x_482_; 
lean_dec(v_c_480_);
v___x_482_ = lean_box(0);
return v___x_482_;
}
else
{
lean_object* v_val_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_val_483_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v___x_481_, 1);
v___x_484_ = lean_array_get_size(v_s_478_);
v___x_485_ = lean_nat_dec_lt(v_val_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec(v_val_483_);
lean_dec(v_c_480_);
v___x_486_ = lean_box(0);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_487_ = lean_array_fget_borrowed(v_s_478_, v_val_483_);
lean_dec(v_val_483_);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_array_get_size(v___x_487_);
v___x_490_ = lean_nat_dec_lt(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v_c_480_);
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_sub(v___x_489_, v___x_492_);
v___x_494_ = lean_nat_dec_le(v___x_488_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v___x_493_);
lean_dec(v_c_480_);
v___x_495_ = lean_box(0);
return v___x_495_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0));
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v_c_480_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v___x_487_, v___x_497_, v___x_488_, v___x_493_);
lean_dec_ref_known(v___x_497_, 2);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v_val_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_val_500_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v___x_498_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_val_500_);
lean_dec(v___x_498_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_snd_504_; lean_object* v___x_506_; 
v_snd_504_ = lean_ctor_get(v_val_500_, 1);
lean_inc(v_snd_504_);
lean_dec(v_val_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v_snd_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_snd_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed(lean_object* v_s_509_, lean_object* v_env_510_, lean_object* v_c_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(v_s_509_, v_env_510_, v_c_511_);
lean_dec_ref(v_env_510_);
lean_dec_ref(v_s_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(lean_object* v_as_513_, lean_object* v_k_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_513_, v_k_514_, v_x_515_, v_x_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___boxed(lean_object* v_as_519_, lean_object* v_k_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(v_as_519_, v_k_520_, v_x_521_, v_x_522_, v_x_523_);
lean_dec_ref(v_k_520_);
lean_dec_ref(v_as_519_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v_x_529_);
lean_dec_ref(v_x_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_box(0);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v_x_533_);
lean_dec_ref(v_x_533_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object* v_s_535_, lean_object* v_x_536_){
_start:
{
lean_inc_ref(v_s_535_);
return v_s_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object* v_s_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v_s_537_, v_x_538_);
lean_dec_ref(v_x_538_);
lean_dec_ref(v_s_537_);
return v_res_539_;
}
}
lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object* v_importedEntries_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_importedEntries_540_);
return v___x_543_;
}
}
LEAN_EXPORT void l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_importedEntries_540_ = stack[0].m_obj;
lean_object* v___y_541_ = stack[1].m_obj;
lean_object* v_res_544_;
v_res_544_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v_importedEntries_540_, v___y_541_);
stack->m_obj
 = v_res_544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object* v_importedEntries_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v_importedEntries_545_, v___y_546_);
lean_dec_ref(v___y_546_);
return v_res_548_;
}
}
lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object* v_exportedEnv_549_, uint8_t v___x_550_, lean_object* v_names_551_, lean_object* v_name_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
lean_inc(v_name_552_);
v___x_554_ = l_Lean_Environment_find_x3f(v_exportedEnv_549_, v_name_552_, v___x_550_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_dec(v_name_552_);
return v_names_551_;
}
else
{
lean_object* v___x_555_; 
lean_dec_ref_known(v___x_554_, 1);
v___x_555_ = lean_array_push(v_names_551_, v_name_552_);
return v___x_555_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_exportedEnv_549_ = stack[0].m_obj;
uint8_t v___x_550_ = stack[1].m_num;
lean_object* v_names_551_ = stack[2].m_obj;
lean_object* v_name_552_ = stack[3].m_obj;
lean_object* v_x_553_ = stack[4].m_obj;
lean_object* v_res_556_;
v_res_556_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v_exportedEnv_549_, v___x_550_, v_names_551_, v_name_552_, v_x_553_);
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object* v_exportedEnv_557_, lean_object* v___x_558_, lean_object* v_names_559_, lean_object* v_name_560_, lean_object* v_x_561_){
_start:
{
uint8_t v___x_1722__boxed_562_; lean_object* v_res_563_; 
v___x_1722__boxed_562_ = lean_unbox(v___x_558_);
v_res_563_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v_exportedEnv_557_, v___x_1722__boxed_562_, v_names_559_, v_name_560_, v_x_561_);
lean_dec_ref(v_x_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_564_, lean_object* v_keys_565_, lean_object* v_vals_566_, lean_object* v_i_567_, lean_object* v_acc_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v_keys_565_);
v___x_570_ = lean_nat_dec_lt(v_i_567_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v_i_567_);
lean_dec(v_f_564_);
return v_acc_568_;
}
else
{
lean_object* v_k_571_; lean_object* v_v_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_k_571_ = lean_array_fget_borrowed(v_keys_565_, v_i_567_);
v_v_572_ = lean_array_fget_borrowed(v_vals_566_, v_i_567_);
lean_inc(v_f_564_);
lean_inc(v_v_572_);
lean_inc(v_k_571_);
v___x_573_ = lean_apply_3(v_f_564_, v_acc_568_, v_k_571_, v_v_572_);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_i_567_, v___x_574_);
lean_dec(v_i_567_);
v_i_567_ = v___x_575_;
v_acc_568_ = v___x_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_577_, lean_object* v_keys_578_, lean_object* v_vals_579_, lean_object* v_i_580_, lean_object* v_acc_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_577_, v_keys_578_, v_vals_579_, v_i_580_, v_acc_581_);
lean_dec_ref(v_vals_579_);
lean_dec_ref(v_keys_578_);
return v_res_582_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_583_, lean_object* v_as_584_, size_t v_i_585_, size_t v_stop_586_, lean_object* v_b_587_){
_start:
{
lean_object* v___y_589_; uint8_t v___x_593_; 
v___x_593_ = lean_usize_dec_eq(v_i_585_, v_stop_586_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_array_uget_borrowed(v_as_584_, v_i_585_);
switch(lean_obj_tag(v___x_594_))
{
case 0:
{
lean_object* v_key_595_; lean_object* v_val_596_; lean_object* v___x_597_; 
v_key_595_ = lean_ctor_get(v___x_594_, 0);
v_val_596_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_f_583_);
lean_inc(v_val_596_);
lean_inc(v_key_595_);
v___x_597_ = lean_apply_3(v_f_583_, v_b_587_, v_key_595_, v_val_596_);
v___y_589_ = v___x_597_;
goto v___jp_588_;
}
case 1:
{
lean_object* v_node_598_; lean_object* v___x_599_; 
v_node_598_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_f_583_);
v___x_599_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_583_, v_node_598_, v_b_587_);
v___y_589_ = v___x_599_;
goto v___jp_588_;
}
default: 
{
v___y_589_ = v_b_587_;
goto v___jp_588_;
}
}
}
else
{
lean_dec(v_f_583_);
return v_b_587_;
}
v___jp_588_:
{
size_t v___x_590_; size_t v___x_591_; 
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_add(v_i_585_, v___x_590_);
v_i_585_ = v___x_591_;
v_b_587_ = v___y_589_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_583_ = stack[0].m_obj;
lean_object* v_as_584_ = stack[1].m_obj;
size_t v_i_585_ = stack[2].m_num;
size_t v_stop_586_ = stack[3].m_num;
lean_object* v_b_587_ = stack[4].m_obj;
lean_object* v_res_600_;
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_583_, v_as_584_, v_i_585_, v_stop_586_, v_b_587_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_f_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v_es_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_es_604_ = lean_ctor_get(v_x_602_, 0);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_array_get_size(v_es_604_);
v___x_607_ = lean_nat_dec_lt(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_dec(v_f_601_);
return v_x_603_;
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_606_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_601_, v_es_604_, v___x_608_, v___x_609_, v_x_603_);
return v___x_610_;
}
}
else
{
lean_object* v_ks_611_; lean_object* v_vs_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_ks_611_ = lean_ctor_get(v_x_602_, 0);
v_vs_612_ = lean_ctor_get(v_x_602_, 1);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_601_, v_ks_611_, v_vs_612_, v___x_613_, v_x_603_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_615_, v_x_616_, v_x_617_);
lean_dec_ref(v_x_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_619_, lean_object* v_as_620_, lean_object* v_i_621_, lean_object* v_stop_622_, lean_object* v_b_623_){
_start:
{
size_t v_i_boxed_624_; size_t v_stop_boxed_625_; lean_object* v_res_626_; 
v_i_boxed_624_ = lean_unbox_usize(v_i_621_);
lean_dec(v_i_621_);
v_stop_boxed_625_ = lean_unbox_usize(v_stop_622_);
lean_dec(v_stop_622_);
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_619_, v_as_620_, v_i_boxed_624_, v_stop_boxed_625_, v_b_623_);
lean_dec_ref(v_as_620_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_f_627_, lean_object* v_x1_628_, lean_object* v_x2_629_, lean_object* v_x3_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_apply_3(v_f_627_, v_x1_628_, v_x2_629_, v_x3_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg(lean_object* v_map_632_, lean_object* v_f_633_, lean_object* v_init_634_){
_start:
{
lean_object* v___f_635_; lean_object* v___x_636_; 
v___f_635_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_635_, 0, v_f_633_);
v___x_636_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_635_, v_map_632_, v_init_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_map_637_, lean_object* v_f_638_, lean_object* v_init_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg(v_map_637_, v_f_638_, v_init_639_);
lean_dec_ref(v_map_637_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* v_hi_641_, lean_object* v_pivot_642_, lean_object* v_as_643_, lean_object* v_i_644_, lean_object* v_k_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_lt(v_k_645_, v_hi_641_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_k_645_);
v___x_647_ = lean_array_fswap(v_as_643_, v_i_644_, v_hi_641_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_i_644_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v_fst_650_; lean_object* v_fst_651_; uint8_t v___x_652_; 
v___x_649_ = lean_array_fget_borrowed(v_as_643_, v_k_645_);
v_fst_650_ = lean_ctor_get(v___x_649_, 0);
v_fst_651_ = lean_ctor_get(v_pivot_642_, 0);
v___x_652_ = l_Lean_Name_quickLt(v_fst_650_, v_fst_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_k_645_, v___x_653_);
lean_dec(v_k_645_);
v_k_645_ = v___x_654_;
goto _start;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = lean_array_fswap(v_as_643_, v_i_644_, v_k_645_);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_add(v_i_644_, v___x_657_);
lean_dec(v_i_644_);
v___x_659_ = lean_nat_add(v_k_645_, v___x_657_);
lean_dec(v_k_645_);
v_as_643_ = v___x_656_;
v_i_644_ = v___x_658_;
v_k_645_ = v___x_659_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* v_hi_661_, lean_object* v_pivot_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_k_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_661_, v_pivot_662_, v_as_663_, v_i_664_, v_k_665_);
lean_dec_ref(v_pivot_662_);
lean_dec(v_hi_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg(lean_object* v_n_667_, lean_object* v_as_668_, lean_object* v_lo_669_, lean_object* v_hi_670_){
_start:
{
lean_object* v___y_672_; uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_lt(v_lo_669_, v_hi_670_);
if (v___x_682_ == 0)
{
lean_dec(v_lo_669_);
return v_as_668_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_mid_685_; lean_object* v___y_687_; lean_object* v___y_693_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_683_ = lean_nat_add(v_lo_669_, v_hi_670_);
v___x_684_ = lean_unsigned_to_nat(1u);
v_mid_685_ = lean_nat_shiftr(v___x_683_, v___x_684_);
lean_dec(v___x_683_);
v___x_698_ = lean_array_fget_borrowed(v_as_668_, v_mid_685_);
v___x_699_ = lean_array_fget_borrowed(v_as_668_, v_lo_669_);
v___x_700_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
v___y_693_ = v_as_668_;
goto v___jp_692_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = lean_array_fswap(v_as_668_, v_lo_669_, v_mid_685_);
v___y_693_ = v___x_701_;
goto v___jp_692_;
}
v___jp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_array_fget_borrowed(v___y_687_, v_mid_685_);
v___x_689_ = lean_array_fget_borrowed(v___y_687_, v_hi_670_);
v___x_690_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec(v_mid_685_);
v___y_672_ = v___y_687_;
goto v___jp_671_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_array_fswap(v___y_687_, v_mid_685_, v_hi_670_);
lean_dec(v_mid_685_);
v___y_672_ = v___x_691_;
goto v___jp_671_;
}
}
v___jp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_array_fget_borrowed(v___y_693_, v_hi_670_);
v___x_695_ = lean_array_fget_borrowed(v___y_693_, v_lo_669_);
v___x_696_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
v___y_687_ = v___y_693_;
goto v___jp_686_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = lean_array_fswap(v___y_693_, v_lo_669_, v_hi_670_);
v___y_687_ = v___x_697_;
goto v___jp_686_;
}
}
}
v___jp_671_:
{
lean_object* v_pivot_673_; lean_object* v___x_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; uint8_t v___x_677_; 
v_pivot_673_ = lean_array_fget(v___y_672_, v_hi_670_);
lean_inc_n(v_lo_669_, 2);
v___x_674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_670_, v_pivot_673_, v___y_672_, v_lo_669_, v_lo_669_);
lean_dec(v_pivot_673_);
v_fst_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_fst_675_);
v_snd_676_ = lean_ctor_get(v___x_674_, 1);
lean_inc(v_snd_676_);
lean_dec_ref(v___x_674_);
v___x_677_ = lean_nat_dec_le(v_hi_670_, v_fst_675_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg(v_n_667_, v_snd_676_, v_lo_669_, v_fst_675_);
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_fst_675_, v___x_679_);
lean_dec(v_fst_675_);
v_as_668_ = v___x_678_;
v_lo_669_ = v___x_680_;
goto _start;
}
else
{
lean_dec(v_fst_675_);
lean_dec(v_lo_669_);
return v_snd_676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_n_702_, lean_object* v_as_703_, lean_object* v_lo_704_, lean_object* v_hi_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg(v_n_702_, v_as_703_, v_lo_704_, v_hi_705_);
lean_dec(v_hi_705_);
lean_dec(v_n_702_);
return v_res_706_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1(lean_object* v_s_707_, size_t v_sz_708_, size_t v_i_709_, lean_object* v_bs_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = lean_usize_dec_lt(v_i_709_, v_sz_708_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v_s_707_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_bs_710_);
lean_ctor_set(v___x_714_, 1, v___y_712_);
return v___x_714_;
}
else
{
lean_object* v_v_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_fst_718_; lean_object* v_snd_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_732_; 
v_v_715_ = lean_array_uget(v_bs_710_, v_i_709_);
lean_inc_ref(v_s_707_);
v___x_716_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed), 3, 1);
lean_closure_set(v___x_716_, 0, v_s_707_);
lean_inc(v_v_715_);
v___x_717_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(v___x_716_, v_v_715_, v___y_711_, v___y_712_);
v_fst_718_ = lean_ctor_get(v___x_717_, 0);
v_snd_719_ = lean_ctor_get(v___x_717_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_732_ == 0)
{
v___x_721_ = v___x_717_;
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_snd_719_);
lean_inc(v_fst_718_);
lean_dec(v___x_717_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_732_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v_bs_x27_724_; lean_object* v___x_726_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_710_, v_i_709_, v___x_723_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_fst_718_);
lean_ctor_set(v___x_721_, 0, v_v_715_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_fst_718_);
v___x_726_ = v_reuseFailAlloc_731_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_709_, v___x_727_);
v___x_729_ = lean_array_uset(v_bs_x27_724_, v_i_709_, v___x_726_);
v_i_709_ = v___x_728_;
v_bs_710_ = v___x_729_;
v___y_712_ = v_snd_719_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_707_ = stack[0].m_obj;
size_t v_sz_708_ = stack[1].m_num;
size_t v_i_709_ = stack[2].m_num;
lean_object* v_bs_710_ = stack[3].m_obj;
lean_object* v___y_711_ = stack[4].m_obj;
lean_object* v___y_712_ = stack[5].m_obj;
lean_object* v_res_733_;
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1(v_s_707_, v_sz_708_, v_i_709_, v_bs_710_, v___y_711_, v___y_712_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1___boxed(lean_object* v_s_734_, lean_object* v_sz_735_, lean_object* v_i_736_, lean_object* v_bs_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
size_t v_sz_boxed_740_; size_t v_i_boxed_741_; lean_object* v_res_742_; 
v_sz_boxed_740_ = lean_unbox_usize(v_sz_735_);
lean_dec(v_sz_735_);
v_i_boxed_741_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1(v_s_734_, v_sz_boxed_740_, v_i_boxed_741_, v_bs_737_, v___y_738_, v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object* v___x_745_, lean_object* v_env_746_, lean_object* v_s_747_){
_start:
{
lean_object* v_checked_748_; lean_object* v___x_749_; lean_object* v_constants_750_; lean_object* v_map_u2082_751_; uint8_t v___x_752_; lean_object* v_exportedEnv_753_; lean_object* v___x_754_; lean_object* v___f_755_; uint8_t v___x_756_; lean_object* v_privateEnv_757_; lean_object* v___x_758_; lean_object* v_allNames_759_; size_t v_sz_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_entries_764_; lean_object* v___x_765_; lean_object* v___y_767_; lean_object* v___y_768_; uint8_t v___x_771_; 
v_checked_748_ = lean_ctor_get(v_env_746_, 2);
lean_inc_ref(v_checked_748_);
v___x_749_ = lean_task_get_own(v_checked_748_);
v_constants_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc_ref(v_constants_750_);
lean_dec(v___x_749_);
v_map_u2082_751_ = lean_ctor_get(v_constants_750_, 1);
lean_inc_ref(v_map_u2082_751_);
lean_dec_ref(v_constants_750_);
v___x_752_ = 1;
lean_inc_ref(v_env_746_);
v_exportedEnv_753_ = l_Lean_Environment_setExporting(v_env_746_, v___x_752_);
v___x_754_ = lean_box(v___x_752_);
v___f_755_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed), 5, 2);
lean_closure_set(v___f_755_, 0, v_exportedEnv_753_);
lean_closure_set(v___f_755_, 1, v___x_754_);
v___x_756_ = 0;
v_privateEnv_757_ = l_Lean_Environment_setExporting(v_env_746_, v___x_756_);
v___x_758_ = lean_mk_empty_array_with_capacity(v___x_745_);
v_allNames_759_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg(v_map_u2082_751_, v___f_755_, v___x_758_);
lean_dec_ref(v_map_u2082_751_);
v_sz_760_ = lean_array_size(v_allNames_759_);
v___x_761_ = lean_box_usize(v_sz_760_);
v___x_762_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_));
v___x_763_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__1___boxed), 6, 4);
lean_closure_set(v___x_763_, 0, v_s_747_);
lean_closure_set(v___x_763_, 1, v___x_761_);
lean_closure_set(v___x_763_, 2, v___x_762_);
lean_closure_set(v___x_763_, 3, v_allNames_759_);
v_entries_764_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(v_privateEnv_757_, v___x_763_);
v___x_765_ = lean_array_get_size(v_entries_764_);
v___x_771_ = lean_nat_dec_eq(v___x_765_, v___x_745_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___y_775_; uint8_t v___x_777_; 
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_sub(v___x_765_, v___x_772_);
v___x_777_ = lean_nat_dec_le(v___x_745_, v___x_773_);
if (v___x_777_ == 0)
{
lean_dec(v___x_745_);
lean_inc(v___x_773_);
v___y_775_ = v___x_773_;
goto v___jp_774_;
}
else
{
v___y_775_ = v___x_745_;
goto v___jp_774_;
}
v___jp_774_:
{
uint8_t v___x_776_; 
v___x_776_ = lean_nat_dec_le(v___y_775_, v___x_773_);
if (v___x_776_ == 0)
{
lean_dec(v___x_773_);
lean_inc(v___y_775_);
v___y_767_ = v___y_775_;
v___y_768_ = v___y_775_;
goto v___jp_766_;
}
else
{
v___y_767_ = v___y_775_;
v___y_768_ = v___x_773_;
goto v___jp_766_;
}
}
}
else
{
lean_object* v___x_778_; 
lean_dec(v___x_745_);
lean_inc_n(v_entries_764_, 2);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v_entries_764_);
lean_ctor_set(v___x_778_, 1, v_entries_764_);
lean_ctor_set(v___x_778_, 2, v_entries_764_);
return v___x_778_;
}
v___jp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg(v___x_765_, v_entries_764_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_inc_ref_n(v___x_769_, 2);
v___x_770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
return v___x_770_;
}
}
}
lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(lean_object* v___x_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
return v___x_781_;
}
}
LEAN_EXPORT void l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_779_ = stack[0].m_obj;
lean_object* v_res_782_;
v_res_782_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v___x_779_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object* v___x_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(v___x_783_);
return v_res_785_;
}
}
lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_));
v___x_835_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT void l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_836_;
v_res_836_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_();
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2____boxed(lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_();
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0(lean_object* v_00_u03c3_839_, lean_object* v_00_u03b2_840_, lean_object* v_map_841_, lean_object* v_f_842_, lean_object* v_init_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___redArg(v_map_841_, v_f_842_, v_init_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03c3_845_, lean_object* v_00_u03b2_846_, lean_object* v_map_847_, lean_object* v_f_848_, lean_object* v_init_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0(v_00_u03c3_845_, v_00_u03b2_846_, v_map_847_, v_f_848_, v_init_849_);
lean_dec_ref(v_map_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2(lean_object* v_n_851_, lean_object* v_as_852_, lean_object* v_lo_853_, lean_object* v_hi_854_, lean_object* v_w_855_, lean_object* v_hlo_856_, lean_object* v_hhi_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___redArg(v_n_851_, v_as_852_, v_lo_853_, v_hi_854_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_859_, lean_object* v_as_860_, lean_object* v_lo_861_, lean_object* v_hi_862_, lean_object* v_w_863_, lean_object* v_hlo_864_, lean_object* v_hhi_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2(v_n_859_, v_as_860_, v_lo_861_, v_hi_862_, v_w_863_, v_hlo_864_, v_hhi_865_);
lean_dec(v_hi_862_);
lean_dec(v_n_859_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_867_, lean_object* v_f_868_, lean_object* v_init_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_868_, v_map_867_, v_init_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_871_, lean_object* v_f_872_, lean_object* v_init_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_871_, v_f_872_, v_init_873_);
lean_dec_ref(v_map_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_875_, lean_object* v_00_u03b2_876_, lean_object* v_map_877_, lean_object* v_f_878_, lean_object* v_init_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_878_, v_map_877_, v_init_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_881_, lean_object* v_00_u03b2_882_, lean_object* v_map_883_, lean_object* v_f_884_, lean_object* v_init_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_881_, v_00_u03b2_882_, v_map_883_, v_f_884_, v_init_885_);
lean_dec_ref(v_map_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3(lean_object* v_n_887_, lean_object* v_lo_888_, lean_object* v_hi_889_, lean_object* v_hhi_890_, lean_object* v_pivot_891_, lean_object* v_as_892_, lean_object* v_i_893_, lean_object* v_k_894_, lean_object* v_ilo_895_, lean_object* v_ik_896_, lean_object* v_w_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_889_, v_pivot_891_, v_as_892_, v_i_893_, v_k_894_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* v_n_899_, lean_object* v_lo_900_, lean_object* v_hi_901_, lean_object* v_hhi_902_, lean_object* v_pivot_903_, lean_object* v_as_904_, lean_object* v_i_905_, lean_object* v_k_906_, lean_object* v_ilo_907_, lean_object* v_ik_908_, lean_object* v_w_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__2_spec__3(v_n_899_, v_lo_900_, v_hi_901_, v_hhi_902_, v_pivot_903_, v_as_904_, v_i_905_, v_k_906_, v_ilo_907_, v_ik_908_, v_w_909_);
lean_dec_ref(v_pivot_903_);
lean_dec(v_hi_901_);
lean_dec(v_lo_900_);
lean_dec(v_n_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_911_, lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_f_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_914_, v_x_915_, v_x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_918_, lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_f_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_918_, v_00_u03b1_919_, v_00_u03b2_920_, v_f_921_, v_x_922_, v_x_923_);
lean_dec_ref(v_x_922_);
return v_res_924_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_00_u03c3_927_, lean_object* v_f_928_, lean_object* v_as_929_, size_t v_i_930_, size_t v_stop_931_, lean_object* v_b_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_928_, v_as_929_, v_i_930_, v_stop_931_, v_b_932_);
return v___x_933_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_928_ = stack[3].m_obj;
lean_object* v_as_929_ = stack[4].m_obj;
size_t v_i_930_ = stack[5].m_num;
size_t v_stop_931_ = stack[6].m_num;
lean_object* v_b_932_ = stack[7].m_obj;
lean_object* v_res_934_;
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_box(0), lean_box(0), lean_box(0), v_f_928_, v_as_929_, v_i_930_, v_stop_931_, v_b_932_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_00_u03c3_937_, lean_object* v_f_938_, lean_object* v_as_939_, lean_object* v_i_940_, lean_object* v_stop_941_, lean_object* v_b_942_){
_start:
{
size_t v_i_boxed_943_; size_t v_stop_boxed_944_; lean_object* v_res_945_; 
v_i_boxed_943_ = lean_unbox_usize(v_i_940_);
lean_dec(v_i_940_);
v_stop_boxed_944_ = lean_unbox_usize(v_stop_941_);
lean_dec(v_stop_941_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b1_935_, v_00_u03b2_936_, v_00_u03c3_937_, v_f_938_, v_as_939_, v_i_boxed_943_, v_stop_boxed_944_, v_b_942_);
lean_dec_ref(v_as_939_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_946_, lean_object* v_00_u03b1_947_, lean_object* v_00_u03b2_948_, lean_object* v_f_949_, lean_object* v_keys_950_, lean_object* v_vals_951_, lean_object* v_heq_952_, lean_object* v_i_953_, lean_object* v_acc_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_949_, v_keys_950_, v_vals_951_, v_i_953_, v_acc_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_956_, lean_object* v_00_u03b1_957_, lean_object* v_00_u03b2_958_, lean_object* v_f_959_, lean_object* v_keys_960_, lean_object* v_vals_961_, lean_object* v_heq_962_, lean_object* v_i_963_, lean_object* v_acc_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_956_, v_00_u03b1_957_, v_00_u03b2_958_, v_f_959_, v_keys_960_, v_vals_961_, v_heq_962_, v_i_963_, v_acc_964_);
lean_dec_ref(v_vals_961_);
lean_dec_ref(v_keys_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object* v___x_966_, lean_object* v_constName_967_, lean_object* v_toPure_968_, lean_object* v_env_969_){
_start:
{
uint8_t v___x_970_; lean_object* v_privateEnv_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_s_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_970_ = 0;
lean_inc_ref(v_env_969_);
v_privateEnv_971_ = l_Lean_Environment_setExporting(v_env_969_, v___x_970_);
v___x_972_ = l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt;
v___x_973_ = lean_box(2);
v___x_974_ = lean_box(0);
v_s_975_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_966_, v___x_972_, v_env_969_, v___x_973_, v___x_974_, v___x_970_);
v___x_976_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed), 3, 1);
lean_closure_set(v___x_976_, 0, v_s_975_);
v___x_977_ = lean_alloc_closure((void*)(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed), 4, 2);
lean_closure_set(v___x_977_, 0, v___x_976_);
lean_closure_set(v___x_977_, 1, v_constName_967_);
v___x_978_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(v_privateEnv_971_, v___x_977_);
v___x_979_ = lean_apply_2(v_toPure_968_, lean_box(0), v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_constName_982_){
_start:
{
lean_object* v_toApplicative_983_; lean_object* v_toBind_984_; lean_object* v_getEnv_985_; lean_object* v_toPure_986_; lean_object* v___x_987_; lean_object* v___f_988_; lean_object* v___x_989_; 
v_toApplicative_983_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_983_);
v_toBind_984_ = lean_ctor_get(v_inst_980_, 1);
lean_inc(v_toBind_984_);
lean_dec_ref(v_inst_980_);
v_getEnv_985_ = lean_ctor_get(v_inst_981_, 0);
lean_inc(v_getEnv_985_);
lean_dec_ref(v_inst_981_);
v_toPure_986_ = lean_ctor_get(v_toApplicative_983_, 1);
lean_inc(v_toPure_986_);
lean_dec_ref(v_toApplicative_983_);
v___x_987_ = ((lean_object*)(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState));
v___f_988_ = lean_alloc_closure((void*)(l_Lean_collectAxioms___redArg___lam__0), 4, 3);
lean_closure_set(v___f_988_, 0, v___x_987_);
lean_closure_set(v___f_988_, 1, v_constName_982_);
lean_closure_set(v___f_988_, 2, v_toPure_986_);
v___x_989_ = lean_apply_4(v_toBind_984_, lean_box(0), lean_box(0), v_getEnv_985_, v___f_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object* v_m_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_constName_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_collectAxioms___redArg(v_inst_991_, v_inst_992_, v_constName_993_);
return v___x_994_;
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
res = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_1665659996____hygCtx___hyg_2_();
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
