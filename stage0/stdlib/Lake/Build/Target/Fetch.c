// Lean compiler output
// Module: Lake.Build.Target.Fetch
// Imports: import Lake.Build.Infos public import Lake.Build.Job.Monad import Lake.Config.Monad import all Lake.Build.Key
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
extern lean_object* l_Lake_instDataKindModule;
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindPackage;
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lake_FacetConfigMap_get_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invalid target '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "': package '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "' not found in workspace"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value;
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value;
static const lean_ctor_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value)}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value;
static const lean_ctor_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value)}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value;
static const lean_ctor_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value)}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13_value;
static const lean_ctor_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3;
static lean_once_cell_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "': module '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "': module target '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "' not found in package '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "': target not found in package '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "': unknown facet '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11_value;
static const lean_ctor_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value),LEAN_SCALAR_PTR_LITERAL(29, 214, 131, 210, 10, 90, 37, 134)}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "': targets of opaque data kinds do not support facets"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Target_fetchIn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "type mismatch in target '"};
static const lean_object* l_Lake_Target_fetchIn___redArg___closed__0 = (const lean_object*)&l_Lake_Target_fetchIn___redArg___closed__0_value;
static const lean_string_object l_Lake_Target_fetchIn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "': expected '"};
static const lean_object* l_Lake_Target_fetchIn___redArg___closed__1 = (const lean_object*)&l_Lake_Target_fetchIn___redArg___closed__1_value;
static const lean_string_object l_Lake_Target_fetchIn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "', got "};
static const lean_object* l_Lake_Target_fetchIn___redArg___closed__2 = (const lean_object*)&l_Lake_Target_fetchIn___redArg___closed__2_value;
static const lean_string_object l_Lake_Target_fetchIn___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l_Lake_Target_fetchIn___redArg___closed__3 = (const lean_object*)&l_Lake_Target_fetchIn___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(lean_object* v_name_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_a_4_, lean_object* v_x_5_, lean_object* v___y_6_){
_start:
{
lean_object* v_baseName_7_; uint8_t v___x_8_; 
v_baseName_7_ = lean_ctor_get(v_a_4_, 1);
v___x_8_ = lean_name_eq(v_baseName_7_, v_name_1_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec_ref(v_a_4_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_2_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec_ref(v___x_2_);
v___x_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_10_, 0, v_a_4_);
v___x_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_3_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(lean_object* v_name_14_, lean_object* v___x_15_, lean_object* v___x_16_, lean_object* v_a_17_, lean_object* v_x_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(v_name_14_, v___x_15_, v___x_16_, v_a_17_, v_x_18_, v___y_19_);
lean_dec_ref(v___y_19_);
lean_dec(v_name_14_);
return v_res_20_;
}
}
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(lean_object* v_defaultPkg_47_, lean_object* v_root_48_, lean_object* v_name_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_a_54_; 
switch(lean_obj_tag(v_name_49_))
{
case 0:
{
lean_object* v___x_70_; 
lean_dec_ref(v_root_48_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_defaultPkg_47_);
lean_ctor_set(v___x_70_, 1, v_a_51_);
return v___x_70_;
}
case 2:
{
lean_object* v_toContext_71_; lean_object* v_packageMap_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_dec_ref(v_defaultPkg_47_);
v_toContext_71_ = lean_ctor_get(v_a_50_, 1);
v_packageMap_72_ = lean_ctor_get(v_toContext_71_, 5);
v___x_73_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(v_name_49_);
lean_inc(v_packageMap_72_);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_73_, v_packageMap_72_, v_name_49_);
if (lean_obj_tag(v___x_74_) == 1)
{
lean_object* v_val_75_; lean_object* v___x_76_; 
lean_dec_ref_known(v_name_49_, 2);
lean_dec_ref(v_root_48_);
v_val_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_val_75_);
lean_ctor_set(v___x_76_, 1, v_a_51_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v___x_74_);
v___x_77_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_78_ = l_Lake_PartialBuildKey_toString(v_root_48_);
v___x_79_ = lean_string_append(v___x_77_, v___x_78_);
lean_dec_ref(v___x_78_);
v___x_80_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_81_ = lean_string_append(v___x_79_, v___x_80_);
v___x_82_ = 1;
v___x_83_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_49_, v___x_82_);
v___x_84_ = lean_string_append(v___x_81_, v___x_83_);
lean_dec_ref(v___x_83_);
v___x_85_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_86_ = lean_string_append(v___x_84_, v___x_85_);
v___x_87_ = 3;
v___x_88_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = lean_array_get_size(v_a_51_);
v___x_90_ = lean_array_push(v_a_51_, v___x_88_);
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
return v___x_91_;
}
}
default: 
{
lean_object* v_toContext_92_; lean_object* v_packages_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___f_97_; size_t v_sz_98_; size_t v___x_99_; lean_object* v___x_100_; lean_object* v_fst_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v_defaultPkg_47_);
v_toContext_92_ = lean_ctor_get(v_a_50_, 1);
v_packages_93_ = lean_ctor_get(v_toContext_92_, 4);
v___x_94_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13));
v___x_95_ = lean_box(0);
v___x_96_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
lean_inc(v_name_49_);
v___f_97_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_97_, 0, v_name_49_);
lean_closure_set(v___f_97_, 1, v___x_96_);
lean_closure_set(v___f_97_, 2, v___x_95_);
v_sz_98_ = lean_array_size(v_packages_93_);
v___x_99_ = ((size_t)0ULL);
lean_inc_ref(v_packages_93_);
v___x_100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_94_, v_packages_93_, v___f_97_, v_sz_98_, v___x_99_, v___x_96_);
v_fst_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v___x_100_, 1);
lean_dec(v_unused_111_);
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_fst_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
if (lean_obj_tag(v_fst_101_) == 0)
{
lean_del_object(v___x_103_);
v_a_54_ = v_a_51_;
goto v___jp_53_;
}
else
{
lean_object* v_val_105_; 
v_val_105_ = lean_ctor_get(v_fst_101_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v_fst_101_, 1);
if (lean_obj_tag(v_val_105_) == 1)
{
lean_object* v_val_106_; lean_object* v___x_108_; 
lean_dec(v_name_49_);
lean_dec_ref(v_root_48_);
v_val_106_ = lean_ctor_get(v_val_105_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v_val_105_, 1);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_a_51_);
lean_ctor_set(v___x_103_, 0, v_val_106_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_val_106_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_a_51_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_dec(v_val_105_);
lean_del_object(v___x_103_);
v_a_54_ = v_a_51_;
goto v___jp_53_;
}
}
}
}
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_55_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_56_ = l_Lake_PartialBuildKey_toString(v_root_48_);
v___x_57_ = lean_string_append(v___x_55_, v___x_56_);
lean_dec_ref(v___x_56_);
v___x_58_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_59_ = lean_string_append(v___x_57_, v___x_58_);
v___x_60_ = 1;
v___x_61_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_49_, v___x_60_);
v___x_62_ = lean_string_append(v___x_59_, v___x_61_);
lean_dec_ref(v___x_61_);
v___x_63_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_64_ = lean_string_append(v___x_62_, v___x_63_);
v___x_65_ = 3;
v___x_66_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*1, v___x_65_);
v___x_67_ = lean_array_get_size(v_a_54_);
v___x_68_ = lean_array_push(v_a_54_, v___x_66_);
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultPkg_47_ = stack[0].m_obj;
lean_object* v_root_48_ = stack[1].m_obj;
lean_object* v_name_49_ = stack[2].m_obj;
lean_object* v_a_50_ = stack[3].m_obj;
lean_object* v_a_51_ = stack[4].m_obj;
lean_object* v_res_112_;
v_res_112_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(v_defaultPkg_47_, v_root_48_, v_name_49_, v_a_50_, v_a_51_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___boxed(lean_object* v_defaultPkg_113_, lean_object* v_root_114_, lean_object* v_name_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(v_defaultPkg_113_, v_root_114_, v_name_115_, v_a_116_, v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_119_;
}
}
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(lean_object* v_defaultPkg_120_, lean_object* v_root_121_, lean_object* v_name_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_a_131_; 
switch(lean_obj_tag(v_name_122_))
{
case 0:
{
lean_object* v___x_147_; 
lean_dec_ref(v_root_121_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v_defaultPkg_120_);
lean_ctor_set(v___x_147_, 1, v_a_128_);
return v___x_147_;
}
case 2:
{
lean_object* v_toContext_148_; lean_object* v_packageMap_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec_ref(v_defaultPkg_120_);
v_toContext_148_ = lean_ctor_get(v_a_127_, 1);
v_packageMap_149_ = lean_ctor_get(v_toContext_148_, 5);
v___x_150_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(v_name_122_);
lean_inc(v_packageMap_149_);
v___x_151_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_150_, v_packageMap_149_, v_name_122_);
if (lean_obj_tag(v___x_151_) == 1)
{
lean_object* v_val_152_; lean_object* v___x_153_; 
lean_dec_ref_known(v_name_122_, 2);
lean_dec_ref(v_root_121_);
v_val_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_val_152_);
lean_ctor_set(v___x_153_, 1, v_a_128_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v___x_151_);
v___x_154_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_155_ = l_Lake_PartialBuildKey_toString(v_root_121_);
v___x_156_ = lean_string_append(v___x_154_, v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
v___x_159_ = 1;
v___x_160_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_122_, v___x_159_);
v___x_161_ = lean_string_append(v___x_158_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_163_ = lean_string_append(v___x_161_, v___x_162_);
v___x_164_ = 3;
v___x_165_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*1, v___x_164_);
v___x_166_ = lean_array_get_size(v_a_128_);
v___x_167_ = lean_array_push(v_a_128_, v___x_165_);
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
return v___x_168_;
}
}
default: 
{
lean_object* v_toContext_169_; lean_object* v_packages_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___f_174_; size_t v_sz_175_; size_t v___x_176_; lean_object* v___x_177_; lean_object* v_fst_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_187_; 
lean_dec_ref(v_defaultPkg_120_);
v_toContext_169_ = lean_ctor_get(v_a_127_, 1);
v_packages_170_ = lean_ctor_get(v_toContext_169_, 4);
v___x_171_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13));
v___x_172_ = lean_box(0);
v___x_173_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
lean_inc(v_name_122_);
v___f_174_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_174_, 0, v_name_122_);
lean_closure_set(v___f_174_, 1, v___x_173_);
lean_closure_set(v___f_174_, 2, v___x_172_);
v_sz_175_ = lean_array_size(v_packages_170_);
v___x_176_ = ((size_t)0ULL);
lean_inc_ref(v_packages_170_);
v___x_177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_171_, v_packages_170_, v___f_174_, v_sz_175_, v___x_176_, v___x_173_);
v_fst_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v___x_177_, 1);
lean_dec(v_unused_188_);
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_fst_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
if (lean_obj_tag(v_fst_178_) == 0)
{
lean_del_object(v___x_180_);
v_a_131_ = v_a_128_;
goto v___jp_130_;
}
else
{
lean_object* v_val_182_; 
v_val_182_ = lean_ctor_get(v_fst_178_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v_fst_178_, 1);
if (lean_obj_tag(v_val_182_) == 1)
{
lean_object* v_val_183_; lean_object* v___x_185_; 
lean_dec(v_name_122_);
lean_dec_ref(v_root_121_);
v_val_183_ = lean_ctor_get(v_val_182_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v_val_182_, 1);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v_a_128_);
lean_ctor_set(v___x_180_, 0, v_val_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_val_183_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_a_128_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
else
{
lean_dec(v_val_182_);
lean_del_object(v___x_180_);
v_a_131_ = v_a_128_;
goto v___jp_130_;
}
}
}
}
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_132_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_133_ = l_Lake_PartialBuildKey_toString(v_root_121_);
v___x_134_ = lean_string_append(v___x_132_, v___x_133_);
lean_dec_ref(v___x_133_);
v___x_135_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_136_ = lean_string_append(v___x_134_, v___x_135_);
v___x_137_ = 1;
v___x_138_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_122_, v___x_137_);
v___x_139_ = lean_string_append(v___x_136_, v___x_138_);
lean_dec_ref(v___x_138_);
v___x_140_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_141_ = lean_string_append(v___x_139_, v___x_140_);
v___x_142_ = 3;
v___x_143_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_142_);
v___x_144_ = lean_array_get_size(v_a_131_);
v___x_145_ = lean_array_push(v_a_131_, v___x_143_);
v___x_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultPkg_120_ = stack[0].m_obj;
lean_object* v_root_121_ = stack[1].m_obj;
lean_object* v_name_122_ = stack[2].m_obj;
lean_object* v_a_123_ = stack[3].m_obj;
lean_object* v_a_124_ = stack[4].m_obj;
lean_object* v_a_125_ = stack[5].m_obj;
lean_object* v_a_126_ = stack[6].m_obj;
lean_object* v_a_127_ = stack[7].m_obj;
lean_object* v_a_128_ = stack[8].m_obj;
lean_object* v_res_189_;
v_res_189_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(v_defaultPkg_120_, v_root_121_, v_name_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(lean_object* v_defaultPkg_190_, lean_object* v_root_191_, lean_object* v_name_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(v_defaultPkg_190_, v_root_191_, v_name_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
return v_res_200_;
}
}
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(lean_object* v_fst_201_, lean_object* v_kind_202_, lean_object* v___x_203_, lean_object* v_data_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_log_212_; uint8_t v_action_213_; uint8_t v_wantsRebuild_214_; uint8_t v_canceled_215_; lean_object* v_trace_216_; lean_object* v_buildTime_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_247_; 
v_log_212_ = lean_ctor_get(v___y_210_, 0);
v_action_213_ = lean_ctor_get_uint8(v___y_210_, sizeof(void*)*3);
v_wantsRebuild_214_ = lean_ctor_get_uint8(v___y_210_, sizeof(void*)*3 + 1);
v_canceled_215_ = lean_ctor_get_uint8(v___y_210_, sizeof(void*)*3 + 2);
v_trace_216_ = lean_ctor_get(v___y_210_, 1);
v_buildTime_217_ = lean_ctor_get(v___y_210_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v___y_210_);
if (v_isSharedCheck_247_ == 0)
{
v___x_219_ = v___y_210_;
v_isShared_220_ = v_isSharedCheck_247_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_buildTime_217_);
lean_inc(v_trace_216_);
lean_inc(v_log_212_);
lean_dec(v___y_210_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_247_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_221_, 0, v_fst_201_);
lean_ctor_set(v___x_221_, 1, v_kind_202_);
lean_ctor_set(v___x_221_, 2, v_data_204_);
lean_ctor_set(v___x_221_, 3, v___x_203_);
lean_inc_ref(v___y_209_);
lean_inc(v___y_208_);
lean_inc(v___y_207_);
lean_inc(v___y_206_);
v___x_222_ = lean_apply_7(v___y_205_, v___x_221_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v_log_212_, lean_box(0));
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_234_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_a_224_ = lean_ctor_get(v___x_222_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_234_ == 0)
{
v___x_226_ = v___x_222_;
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v_a_224_);
v___x_229_ = v___x_219_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_224_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_trace_216_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_buildTime_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_233_, sizeof(void*)*3, v_action_213_);
lean_ctor_set_uint8(v_reuseFailAlloc_233_, sizeof(void*)*3 + 1, v_wantsRebuild_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_233_, sizeof(void*)*3 + 2, v_canceled_215_);
v___x_229_ = v_reuseFailAlloc_233_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_229_);
v___x_231_ = v___x_226_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_223_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_235_; lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_246_; 
v_a_235_ = lean_ctor_get(v___x_222_, 0);
v_a_236_ = lean_ctor_get(v___x_222_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_246_ == 0)
{
v___x_238_ = v___x_222_;
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_inc(v_a_235_);
lean_dec(v___x_222_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_246_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v_a_236_);
v___x_241_ = v___x_219_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_236_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_trace_216_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_buildTime_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*3, v_action_213_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*3 + 1, v_wantsRebuild_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_245_, sizeof(void*)*3 + 2, v_canceled_215_);
v___x_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_241_);
v___x_243_ = v___x_238_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_201_ = stack[0].m_obj;
lean_object* v_kind_202_ = stack[1].m_obj;
lean_object* v___x_203_ = stack[2].m_obj;
lean_object* v_data_204_ = stack[3].m_obj;
lean_object* v___y_205_ = stack[4].m_obj;
lean_object* v___y_206_ = stack[5].m_obj;
lean_object* v___y_207_ = stack[6].m_obj;
lean_object* v___y_208_ = stack[7].m_obj;
lean_object* v___y_209_ = stack[8].m_obj;
lean_object* v___y_210_ = stack[9].m_obj;
lean_object* v_res_248_;
v_res_248_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(v_fst_201_, v_kind_202_, v___x_203_, v_data_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object* v_fst_249_, lean_object* v_kind_250_, lean_object* v___x_251_, lean_object* v_data_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(v_fst_249_, v_kind_250_, v___x_251_, v_data_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec(v___y_255_);
lean_dec(v___y_254_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(lean_object* v_t_261_, lean_object* v_k_262_){
_start:
{
if (lean_obj_tag(v_t_261_) == 0)
{
lean_object* v_k_263_; lean_object* v_v_264_; lean_object* v_l_265_; lean_object* v_r_266_; uint8_t v___x_267_; 
v_k_263_ = lean_ctor_get(v_t_261_, 1);
v_v_264_ = lean_ctor_get(v_t_261_, 2);
v_l_265_ = lean_ctor_get(v_t_261_, 3);
v_r_266_ = lean_ctor_get(v_t_261_, 4);
v___x_267_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_262_, v_k_263_);
switch(v___x_267_)
{
case 0:
{
v_t_261_ = v_l_265_;
goto _start;
}
case 1:
{
lean_object* v___x_269_; 
lean_inc(v_v_264_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_v_264_);
return v___x_269_;
}
default: 
{
v_t_261_ = v_r_266_;
goto _start;
}
}
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_box(0);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(lean_object* v_t_272_, lean_object* v_k_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_272_, v_k_273_);
lean_dec(v_k_273_);
lean_dec(v_t_272_);
return v_res_274_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(lean_object* v_package_275_, lean_object* v_as_276_, size_t v_sz_277_, size_t v_i_278_, lean_object* v_b_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_usize_dec_lt(v_i_278_, v_sz_277_);
if (v___x_280_ == 0)
{
lean_inc_ref(v_b_279_);
return v_b_279_;
}
else
{
lean_object* v_a_281_; lean_object* v_baseName_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v_a_281_ = lean_array_uget_borrowed(v_as_276_, v_i_278_);
v_baseName_282_ = lean_ctor_get(v_a_281_, 1);
v___x_283_ = lean_box(0);
v___x_284_ = lean_name_eq(v_baseName_282_, v_package_275_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; 
v___x_285_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_add(v_i_278_, v___x_286_);
v_i_278_ = v___x_287_;
v_b_279_ = v___x_285_;
goto _start;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_inc(v_a_281_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_a_281_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_283_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_package_275_ = stack[0].m_obj;
lean_object* v_as_276_ = stack[1].m_obj;
size_t v_sz_277_ = stack[2].m_num;
size_t v_i_278_ = stack[3].m_num;
lean_object* v_b_279_ = stack[4].m_obj;
lean_object* v_res_292_;
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_275_, v_as_276_, v_sz_277_, v_i_278_, v_b_279_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(lean_object* v_package_293_, lean_object* v_as_294_, lean_object* v_sz_295_, lean_object* v_i_296_, lean_object* v_b_297_){
_start:
{
size_t v_sz_boxed_298_; size_t v_i_boxed_299_; lean_object* v_res_300_; 
v_sz_boxed_298_ = lean_unbox_usize(v_sz_295_);
lean_dec(v_sz_295_);
v_i_boxed_299_ = lean_unbox_usize(v_i_296_);
lean_dec(v_i_296_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_293_, v_as_294_, v_sz_boxed_298_, v_i_boxed_299_, v_b_297_);
lean_dec_ref(v_b_297_);
lean_dec_ref(v_as_294_);
lean_dec(v_package_293_);
return v_res_300_;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2));
v___x_306_ = l_Lake_BuildTrace_nil(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_309_ = 0;
v___x_310_ = 0;
v___x_311_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0));
v___x_312_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_308_);
lean_ctor_set(v___x_312_, 2, v___x_307_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*3, v___x_310_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*3 + 1, v___x_309_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*3 + 2, v___x_309_);
return v___x_312_;
}
}
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object* v_defaultPkg_323_, lean_object* v_root_324_, lean_object* v_self_325_, uint8_t v_facetless_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_a_335_; lean_object* v_a_336_; lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v_a_343_; lean_object* v_a_344_; lean_object* v___x_346_; 
v___x_346_ = l_Lake_instDataKindModule;
switch(lean_obj_tag(v_self_325_))
{
case 0:
{
lean_object* v_module_347_; lean_object* v_toContext_348_; lean_object* v___x_349_; 
lean_dec_ref(v_a_327_);
lean_dec_ref(v_defaultPkg_323_);
v_module_347_ = lean_ctor_get(v_self_325_, 0);
lean_inc_n(v_module_347_, 2);
lean_dec_ref_known(v_self_325_, 1);
v_toContext_348_ = lean_ctor_get(v_a_331_, 1);
v___x_349_ = l_Lake_Workspace_findModule_x3f(v_module_347_, v_toContext_348_);
if (lean_obj_tag(v___x_349_) == 1)
{
lean_object* v_val_350_; lean_object* v_lib_351_; lean_object* v_pkg_352_; lean_object* v_keyName_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_dec_ref(v_root_324_);
v_val_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v___x_349_, 1);
v_lib_351_ = lean_ctor_get(v_val_350_, 0);
v_pkg_352_ = lean_ctor_get(v_lib_351_, 0);
v_keyName_353_ = lean_ctor_get(v_pkg_352_, 2);
lean_inc(v_keyName_353_);
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v_keyName_353_);
lean_ctor_set(v___x_354_, 1, v_module_347_);
v___x_355_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_356_ = 0;
v___x_357_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v_val_350_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = lean_task_pure(v___x_358_);
v___x_360_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___x_346_);
lean_ctor_set(v___x_360_, 2, v___x_355_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*3, v___x_356_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_354_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_a_332_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v___x_349_);
v___x_363_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_364_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_365_ = lean_string_append(v___x_363_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_366_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
v___x_368_ = 1;
v___x_369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_347_, v___x_368_);
v___x_370_ = lean_string_append(v___x_367_, v___x_369_);
lean_dec_ref(v___x_369_);
v___x_371_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
v___x_373_ = 3;
v___x_374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*1, v___x_373_);
v___x_375_ = lean_array_get_size(v_a_332_);
v___x_376_ = lean_array_push(v_a_332_, v___x_374_);
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
return v___x_377_;
}
}
case 1:
{
lean_object* v_package_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_a_327_);
v_package_378_ = lean_ctor_get(v_self_325_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_self_325_);
if (v_isSharedCheck_441_ == 0)
{
v___x_380_ = v_self_325_;
v_isShared_381_ = v_isSharedCheck_441_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_package_378_);
lean_dec(v_self_325_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_441_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_a_383_; lean_object* v___x_398_; lean_object* v_a_400_; lean_object* v_a_401_; 
v___x_398_ = l_Lake_instDataKindPackage;
switch(lean_obj_tag(v_package_378_))
{
case 0:
{
lean_dec_ref(v_root_324_);
v_a_400_ = v_defaultPkg_323_;
v_a_401_ = v_a_332_;
goto v___jp_399_;
}
case 2:
{
lean_object* v_toContext_414_; lean_object* v_packageMap_415_; lean_object* v___x_416_; 
lean_dec_ref(v_defaultPkg_323_);
v_toContext_414_ = lean_ctor_get(v_a_331_, 1);
v_packageMap_415_ = lean_ctor_get(v_toContext_414_, 5);
v___x_416_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_415_, v_package_378_);
if (lean_obj_tag(v___x_416_) == 1)
{
lean_object* v_val_417_; 
lean_dec_ref_known(v_package_378_, 2);
lean_dec_ref(v_root_324_);
v_val_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_val_417_);
lean_dec_ref_known(v___x_416_, 1);
v_a_400_ = v_val_417_;
v_a_401_ = v_a_332_;
goto v___jp_399_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v___x_416_);
lean_del_object(v___x_380_);
v___x_418_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_419_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
lean_dec_ref(v___x_419_);
v___x_421_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
v___x_423_ = 1;
v___x_424_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_378_, v___x_423_);
v___x_425_ = lean_string_append(v___x_422_, v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_427_ = lean_string_append(v___x_425_, v___x_426_);
v___x_428_ = 3;
v___x_429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*1, v___x_428_);
v___x_430_ = lean_array_get_size(v_a_332_);
v___x_431_ = lean_array_push(v_a_332_, v___x_429_);
v_a_343_ = v___x_430_;
v_a_344_ = v___x_431_;
goto v___jp_342_;
}
}
default: 
{
lean_object* v_toContext_432_; lean_object* v_packages_433_; lean_object* v___x_434_; size_t v_sz_435_; size_t v___x_436_; lean_object* v___x_437_; lean_object* v_fst_438_; 
lean_dec_ref(v_defaultPkg_323_);
v_toContext_432_ = lean_ctor_get(v_a_331_, 1);
v_packages_433_ = lean_ctor_get(v_toContext_432_, 4);
v___x_434_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_435_ = lean_array_size(v_packages_433_);
v___x_436_ = ((size_t)0ULL);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_378_, v_packages_433_, v_sz_435_, v___x_436_, v___x_434_);
v_fst_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_fst_438_);
lean_dec_ref(v___x_437_);
if (lean_obj_tag(v_fst_438_) == 0)
{
lean_del_object(v___x_380_);
v_a_383_ = v_a_332_;
goto v___jp_382_;
}
else
{
lean_object* v_val_439_; 
v_val_439_ = lean_ctor_get(v_fst_438_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v_fst_438_, 1);
if (lean_obj_tag(v_val_439_) == 1)
{
lean_object* v_val_440_; 
lean_dec(v_package_378_);
lean_dec_ref(v_root_324_);
v_val_440_ = lean_ctor_get(v_val_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_val_439_, 1);
v_a_400_ = v_val_440_;
v_a_401_ = v_a_332_;
goto v___jp_399_;
}
else
{
lean_dec(v_val_439_);
lean_del_object(v___x_380_);
v_a_383_ = v_a_332_;
goto v___jp_382_;
}
}
}
}
v___jp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_384_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_385_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_386_ = lean_string_append(v___x_384_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
v___x_389_ = 1;
v___x_390_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_378_, v___x_389_);
v___x_391_ = lean_string_append(v___x_388_, v___x_390_);
lean_dec_ref(v___x_390_);
v___x_392_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = 3;
v___x_395_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*1, v___x_394_);
v___x_396_ = lean_array_get_size(v_a_383_);
v___x_397_ = lean_array_push(v_a_383_, v___x_395_);
v_a_343_ = v___x_396_;
v_a_344_ = v___x_397_;
goto v___jp_342_;
}
v___jp_399_:
{
lean_object* v_keyName_402_; lean_object* v___x_404_; 
v_keyName_402_ = lean_ctor_get(v_a_400_, 2);
lean_inc(v_keyName_402_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v_keyName_402_);
v___x_404_ = v___x_380_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_keyName_402_);
v___x_404_ = v_reuseFailAlloc_413_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_405_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_406_ = 0;
v___x_407_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_a_400_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_task_pure(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_398_);
lean_ctor_set(v___x_410_, 2, v___x_405_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3, v___x_406_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_404_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_a_401_);
return v___x_412_;
}
}
}
}
case 2:
{
lean_object* v_package_442_; lean_object* v_module_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v_a_327_);
v_package_442_ = lean_ctor_get(v_self_325_, 0);
v_module_443_ = lean_ctor_get(v_self_325_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_self_325_);
if (v_isSharedCheck_528_ == 0)
{
v___x_445_ = v_self_325_;
v_isShared_446_ = v_isSharedCheck_528_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_module_443_);
lean_inc(v_package_442_);
lean_dec(v_self_325_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_528_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_a_448_; lean_object* v_a_449_; lean_object* v_a_486_; 
switch(lean_obj_tag(v_package_442_))
{
case 0:
{
v_a_448_ = v_defaultPkg_323_;
v_a_449_ = v_a_332_;
goto v___jp_447_;
}
case 2:
{
lean_object* v_toContext_501_; lean_object* v_packageMap_502_; lean_object* v___x_503_; 
lean_dec_ref(v_defaultPkg_323_);
v_toContext_501_ = lean_ctor_get(v_a_331_, 1);
v_packageMap_502_ = lean_ctor_get(v_toContext_501_, 5);
v___x_503_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_502_, v_package_442_);
if (lean_obj_tag(v___x_503_) == 1)
{
lean_object* v_val_504_; 
lean_dec_ref_known(v_package_442_, 2);
v_val_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v___x_503_, 1);
v_a_448_ = v_val_504_;
v_a_449_ = v_a_332_;
goto v___jp_447_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v___x_503_);
lean_del_object(v___x_445_);
lean_dec(v_module_443_);
v___x_505_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_506_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_507_ = lean_string_append(v___x_505_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_509_ = lean_string_append(v___x_507_, v___x_508_);
v___x_510_ = 1;
v___x_511_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_442_, v___x_510_);
v___x_512_ = lean_string_append(v___x_509_, v___x_511_);
lean_dec_ref(v___x_511_);
v___x_513_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_514_ = lean_string_append(v___x_512_, v___x_513_);
v___x_515_ = 3;
v___x_516_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*1, v___x_515_);
v___x_517_ = lean_array_get_size(v_a_332_);
v___x_518_ = lean_array_push(v_a_332_, v___x_516_);
v_a_339_ = v___x_517_;
v_a_340_ = v___x_518_;
goto v___jp_338_;
}
}
default: 
{
lean_object* v_toContext_519_; lean_object* v_packages_520_; lean_object* v___x_521_; size_t v_sz_522_; size_t v___x_523_; lean_object* v___x_524_; lean_object* v_fst_525_; 
lean_dec_ref(v_defaultPkg_323_);
v_toContext_519_ = lean_ctor_get(v_a_331_, 1);
v_packages_520_ = lean_ctor_get(v_toContext_519_, 4);
v___x_521_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_522_ = lean_array_size(v_packages_520_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_442_, v_packages_520_, v_sz_522_, v___x_523_, v___x_521_);
v_fst_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_fst_525_);
lean_dec_ref(v___x_524_);
if (lean_obj_tag(v_fst_525_) == 0)
{
lean_del_object(v___x_445_);
lean_dec(v_module_443_);
v_a_486_ = v_a_332_;
goto v___jp_485_;
}
else
{
lean_object* v_val_526_; 
v_val_526_ = lean_ctor_get(v_fst_525_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v_fst_525_, 1);
if (lean_obj_tag(v_val_526_) == 1)
{
lean_object* v_val_527_; 
lean_dec(v_package_442_);
v_val_527_ = lean_ctor_get(v_val_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v_val_526_, 1);
v_a_448_ = v_val_527_;
v_a_449_ = v_a_332_;
goto v___jp_447_;
}
else
{
lean_dec(v_val_526_);
lean_del_object(v___x_445_);
lean_dec(v_module_443_);
v_a_486_ = v_a_332_;
goto v___jp_485_;
}
}
}
}
v___jp_447_:
{
lean_object* v___x_450_; 
lean_inc_ref(v_a_448_);
lean_inc(v_module_443_);
v___x_450_ = l_Lake_Package_findTargetModule_x3f(v_module_443_, v_a_448_);
if (lean_obj_tag(v___x_450_) == 1)
{
lean_object* v_val_451_; lean_object* v_keyName_452_; lean_object* v___x_454_; 
lean_dec_ref(v_root_324_);
v_val_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v___x_450_, 1);
v_keyName_452_ = lean_ctor_get(v_a_448_, 2);
lean_inc(v_keyName_452_);
lean_dec_ref(v_a_448_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_keyName_452_);
v___x_454_ = v___x_445_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_keyName_452_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_module_443_);
v___x_454_ = v_reuseFailAlloc_463_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_455_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_456_ = 0;
v___x_457_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_val_451_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_task_pure(v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_346_);
lean_ctor_set(v___x_460_, 2, v___x_455_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*3, v___x_456_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_454_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v_a_449_);
return v___x_462_;
}
}
else
{
lean_object* v_baseName_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_450_);
lean_del_object(v___x_445_);
v_baseName_464_ = lean_ctor_get(v_a_448_, 1);
lean_inc(v_baseName_464_);
lean_dec_ref(v_a_448_);
v___x_465_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_466_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_467_ = lean_string_append(v___x_465_, v___x_466_);
lean_dec_ref(v___x_466_);
v___x_468_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6));
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
v___x_470_ = 1;
v___x_471_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_443_, v___x_470_);
v___x_472_ = lean_string_append(v___x_469_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v___x_475_ = 0;
v___x_476_ = l_Lean_Name_toString(v_baseName_464_, v___x_475_);
v___x_477_ = lean_string_append(v___x_474_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
v___x_480_ = 3;
v___x_481_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set_uint8(v___x_481_, sizeof(void*)*1, v___x_480_);
v___x_482_ = lean_array_get_size(v_a_449_);
v___x_483_ = lean_array_push(v_a_449_, v___x_481_);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
return v___x_484_;
}
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_487_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_488_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_489_ = lean_string_append(v___x_487_, v___x_488_);
lean_dec_ref(v___x_488_);
v___x_490_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_491_ = lean_string_append(v___x_489_, v___x_490_);
v___x_492_ = 1;
v___x_493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_442_, v___x_492_);
v___x_494_ = lean_string_append(v___x_491_, v___x_493_);
lean_dec_ref(v___x_493_);
v___x_495_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_496_ = lean_string_append(v___x_494_, v___x_495_);
v___x_497_ = 3;
v___x_498_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*1, v___x_497_);
v___x_499_ = lean_array_get_size(v_a_486_);
v___x_500_ = lean_array_push(v_a_486_, v___x_498_);
v_a_339_ = v___x_499_;
v_a_340_ = v___x_500_;
goto v___jp_338_;
}
}
}
case 3:
{
lean_object* v_package_529_; lean_object* v_target_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_680_; 
v_package_529_ = lean_ctor_get(v_self_325_, 0);
v_target_530_ = lean_ctor_get(v_self_325_, 1);
v_isSharedCheck_680_ = !lean_is_exclusive(v_self_325_);
if (v_isSharedCheck_680_ == 0)
{
v___x_532_ = v_self_325_;
v_isShared_533_ = v_isSharedCheck_680_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_target_530_);
lean_inc(v_package_529_);
lean_dec(v_self_325_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_680_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_a_535_; lean_object* v_a_536_; lean_object* v_a_638_; 
switch(lean_obj_tag(v_package_529_))
{
case 0:
{
v_a_535_ = v_defaultPkg_323_;
v_a_536_ = v_a_332_;
goto v___jp_534_;
}
case 2:
{
lean_object* v_toContext_653_; lean_object* v_packageMap_654_; lean_object* v___x_655_; 
lean_dec_ref(v_defaultPkg_323_);
v_toContext_653_ = lean_ctor_get(v_a_331_, 1);
v_packageMap_654_ = lean_ctor_get(v_toContext_653_, 5);
v___x_655_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_654_, v_package_529_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; 
lean_dec_ref_known(v_package_529_, 2);
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v___x_655_, 1);
v_a_535_ = v_val_656_;
v_a_536_ = v_a_332_;
goto v___jp_534_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v___x_655_);
lean_del_object(v___x_532_);
lean_dec(v_target_530_);
lean_dec_ref(v_a_327_);
v___x_657_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_658_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
v___x_662_ = 1;
v___x_663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_529_, v___x_662_);
v___x_664_ = lean_string_append(v___x_661_, v___x_663_);
lean_dec_ref(v___x_663_);
v___x_665_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_666_ = lean_string_append(v___x_664_, v___x_665_);
v___x_667_ = 3;
v___x_668_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*1, v___x_667_);
v___x_669_ = lean_array_get_size(v_a_332_);
v___x_670_ = lean_array_push(v_a_332_, v___x_668_);
v_a_335_ = v___x_669_;
v_a_336_ = v___x_670_;
goto v___jp_334_;
}
}
default: 
{
lean_object* v_toContext_671_; lean_object* v_packages_672_; lean_object* v___x_673_; size_t v_sz_674_; size_t v___x_675_; lean_object* v___x_676_; lean_object* v_fst_677_; 
lean_dec_ref(v_defaultPkg_323_);
v_toContext_671_ = lean_ctor_get(v_a_331_, 1);
v_packages_672_ = lean_ctor_get(v_toContext_671_, 4);
v___x_673_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_674_ = lean_array_size(v_packages_672_);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_529_, v_packages_672_, v_sz_674_, v___x_675_, v___x_673_);
v_fst_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_fst_677_);
lean_dec_ref(v___x_676_);
if (lean_obj_tag(v_fst_677_) == 0)
{
lean_del_object(v___x_532_);
lean_dec(v_target_530_);
lean_dec_ref(v_a_327_);
v_a_638_ = v_a_332_;
goto v___jp_637_;
}
else
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v_fst_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v_fst_677_, 1);
if (lean_obj_tag(v_val_678_) == 1)
{
lean_object* v_val_679_; 
lean_dec(v_package_529_);
v_val_679_ = lean_ctor_get(v_val_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_val_678_, 1);
v_a_535_ = v_val_679_;
v_a_536_ = v_a_332_;
goto v___jp_534_;
}
else
{
lean_dec(v_val_678_);
lean_del_object(v___x_532_);
lean_dec(v_target_530_);
lean_dec_ref(v_a_327_);
v_a_638_ = v_a_332_;
goto v___jp_637_;
}
}
}
}
v___jp_534_:
{
lean_object* v_baseName_537_; lean_object* v_keyName_538_; lean_object* v___x_540_; 
v_baseName_537_ = lean_ctor_get(v_a_535_, 1);
v_keyName_538_ = lean_ctor_get(v_a_535_, 2);
lean_inc(v_target_530_);
lean_inc(v_keyName_538_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_keyName_538_);
v___x_540_ = v___x_532_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_keyName_538_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_target_530_);
v___x_540_ = v_reuseFailAlloc_636_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
if (v_facetless_326_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v_root_324_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_a_535_);
lean_ctor_set(v___x_541_, 1, v_target_530_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc(v_a_329_);
lean_inc(v_a_328_);
v___x_542_ = lean_apply_7(v_a_327_, v___x_541_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_536_, lean_box(0));
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_a_544_ = lean_ctor_get(v___x_542_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_552_ == 0)
{
v___x_546_ = v___x_542_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_540_);
lean_ctor_set(v___x_548_, 1, v_a_543_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_a_544_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v___x_540_);
v_a_553_ = lean_ctor_get(v___x_542_, 0);
v_a_554_ = lean_ctor_get(v___x_542_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_542_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_inc(v_a_553_);
lean_dec(v___x_542_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_553_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v___x_562_; 
v___x_562_ = l_Lake_Package_findTargetDecl_x3f(v_target_530_, v_a_535_);
if (lean_obj_tag(v___x_562_) == 1)
{
lean_object* v_val_563_; lean_object* v_name_564_; lean_object* v_kind_565_; lean_object* v_config_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_root_324_);
v_val_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v___x_562_, 1);
v_name_564_ = lean_ctor_get(v_val_563_, 1);
v_kind_565_ = lean_ctor_get(v_val_563_, 2);
v_config_566_ = lean_ctor_get(v_val_563_, 3);
v_isSharedCheck_619_ = !lean_is_exclusive(v_val_563_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_val_563_, 0);
lean_dec(v_unused_620_);
v___x_568_ = v_val_563_;
v_isShared_569_ = v_isSharedCheck_619_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_config_566_);
lean_inc(v_kind_565_);
lean_inc(v_name_564_);
lean_dec(v_val_563_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_619_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
uint8_t v___x_570_; 
v___x_570_ = l_Lean_Name_isAnonymous(v_kind_565_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec(v_target_530_);
v___x_571_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9));
lean_inc(v_kind_565_);
v___x_572_ = l_Lean_Name_str___override(v_kind_565_, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v_a_535_);
lean_ctor_set(v___x_573_, 1, v_name_564_);
lean_ctor_set(v___x_573_, 2, v_config_566_);
lean_inc(v___x_572_);
lean_inc_ref(v___x_540_);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 1);
lean_ctor_set(v___x_568_, 3, v___x_572_);
lean_ctor_set(v___x_568_, 2, v___x_573_);
lean_ctor_set(v___x_568_, 1, v_kind_565_);
lean_ctor_set(v___x_568_, 0, v___x_540_);
v___x_575_ = v___x_568_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_kind_565_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v___x_572_);
v___x_575_ = v_reuseFailAlloc_597_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc(v_a_329_);
lean_inc(v_a_328_);
v___x_576_ = lean_apply_7(v_a_327_, v___x_575_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_536_, lean_box(0));
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_587_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_a_578_ = lean_ctor_get(v___x_576_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_587_ == 0)
{
v___x_580_ = v___x_576_;
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_540_);
lean_ctor_set(v___x_582_, 1, v___x_572_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_a_577_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_583_);
v___x_585_ = v___x_580_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_578_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v___x_572_);
lean_dec_ref(v___x_540_);
v_a_588_ = lean_ctor_get(v___x_576_, 0);
v_a_589_ = lean_ctor_get(v___x_576_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_576_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_inc(v_a_588_);
lean_dec(v___x_576_);
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
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_588_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_a_589_);
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
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_del_object(v___x_568_);
lean_dec(v_config_566_);
lean_dec(v_kind_565_);
lean_dec(v_name_564_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_a_535_);
lean_ctor_set(v___x_598_, 1, v_target_530_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc(v_a_329_);
lean_inc(v_a_328_);
v___x_599_ = lean_apply_7(v_a_327_, v___x_598_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_536_, lean_box(0));
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_a_601_ = lean_ctor_get(v___x_599_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v___x_599_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_540_);
lean_ctor_set(v___x_605_, 1, v_a_600_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_601_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec_ref(v___x_540_);
v_a_610_ = lean_ctor_get(v___x_599_, 0);
v_a_611_ = lean_ctor_get(v___x_599_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_599_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_inc(v_a_610_);
lean_dec(v___x_599_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_610_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_inc(v_baseName_537_);
lean_dec(v___x_562_);
lean_dec_ref(v___x_540_);
lean_dec_ref(v_a_535_);
lean_dec(v_target_530_);
lean_dec_ref(v_a_327_);
v___x_621_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_622_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_623_ = lean_string_append(v___x_621_, v___x_622_);
lean_dec_ref(v___x_622_);
v___x_624_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10));
v___x_625_ = lean_string_append(v___x_623_, v___x_624_);
v___x_626_ = 0;
v___x_627_ = l_Lean_Name_toString(v_baseName_537_, v___x_626_);
v___x_628_ = lean_string_append(v___x_625_, v___x_627_);
lean_dec_ref(v___x_627_);
v___x_629_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_630_ = lean_string_append(v___x_628_, v___x_629_);
v___x_631_ = 3;
v___x_632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_631_);
v___x_633_ = lean_array_get_size(v_a_536_);
v___x_634_ = lean_array_push(v_a_536_, v___x_632_);
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
return v___x_635_;
}
}
}
}
v___jp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_639_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_640_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
v___x_644_ = 1;
v___x_645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_529_, v___x_644_);
v___x_646_ = lean_string_append(v___x_643_, v___x_645_);
lean_dec_ref(v___x_645_);
v___x_647_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_648_ = lean_string_append(v___x_646_, v___x_647_);
v___x_649_ = 3;
v___x_650_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*1, v___x_649_);
v___x_651_ = lean_array_get_size(v_a_638_);
v___x_652_ = lean_array_push(v_a_638_, v___x_650_);
v_a_335_ = v___x_651_;
v_a_336_ = v___x_652_;
goto v___jp_334_;
}
}
}
default: 
{
lean_object* v_target_681_; lean_object* v_facet_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_754_; 
v_target_681_ = lean_ctor_get(v_self_325_, 0);
v_facet_682_ = lean_ctor_get(v_self_325_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_self_325_);
if (v_isSharedCheck_754_ == 0)
{
v___x_684_ = v_self_325_;
v_isShared_685_ = v_isSharedCheck_754_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_facet_682_);
lean_inc(v_target_681_);
lean_dec(v_self_325_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_754_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; lean_object* v___x_687_; 
v___x_686_ = 0;
lean_inc_ref(v_a_327_);
lean_inc_ref(v_root_324_);
v___x_687_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_323_, v_root_324_, v_target_681_, v___x_686_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v_snd_689_; lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_752_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
v_snd_689_ = lean_ctor_get(v_a_688_, 1);
lean_inc(v_snd_689_);
v_a_690_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v___x_687_, 0);
lean_dec(v_unused_753_);
v___x_692_ = v___x_687_;
v_isShared_693_ = v_isSharedCheck_752_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_687_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_752_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_750_; 
v_fst_694_ = lean_ctor_get(v_a_688_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v_a_688_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v_a_688_, 1);
lean_dec(v_unused_751_);
v___x_696_ = v_a_688_;
v_isShared_697_ = v_isSharedCheck_750_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_fst_694_);
lean_dec(v_a_688_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_750_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_kind_698_; lean_object* v___y_700_; uint8_t v___x_737_; 
v_kind_698_ = lean_ctor_get(v_snd_689_, 1);
v___x_737_ = l_Lean_Name_isAnonymous(v_kind_698_);
if (v___x_737_ == 0)
{
uint8_t v___x_738_; 
v___x_738_ = l_Lean_Name_isAnonymous(v_facet_682_);
if (v___x_738_ == 0)
{
v___y_700_ = v_facet_682_;
goto v___jp_699_;
}
else
{
lean_object* v___x_739_; 
lean_dec(v_facet_682_);
v___x_739_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12));
v___y_700_ = v___x_739_;
goto v___jp_699_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_del_object(v___x_696_);
lean_dec(v_fst_694_);
lean_del_object(v___x_692_);
lean_dec(v_snd_689_);
lean_del_object(v___x_684_);
lean_dec(v_facet_682_);
lean_dec_ref(v_a_327_);
v___x_740_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_741_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_742_ = lean_string_append(v___x_740_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
v___x_744_ = lean_string_append(v___x_742_, v___x_743_);
v___x_745_ = 3;
v___x_746_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*1, v___x_745_);
v___x_747_ = lean_array_get_size(v_a_690_);
v___x_748_ = lean_array_push(v_a_690_, v___x_746_);
v___x_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
return v___x_749_;
}
v___jp_699_:
{
lean_object* v_toContext_701_; lean_object* v_facetConfigs_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_toContext_701_ = lean_ctor_get(v_a_331_, 1);
v_facetConfigs_702_ = lean_ctor_get(v_toContext_701_, 6);
lean_inc(v_kind_698_);
v___x_703_ = l_Lean_Name_append(v_kind_698_, v___y_700_);
v___x_704_ = l_Lake_FacetConfigMap_get_x3f(v___x_703_, v_facetConfigs_702_);
if (lean_obj_tag(v___x_704_) == 1)
{
lean_object* v_val_705_; lean_object* v_outKind_706_; lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
lean_dec_ref(v_root_324_);
v_val_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_704_, 1);
v_outKind_706_ = lean_ctor_get(v_val_705_, 2);
lean_inc(v_outKind_706_);
lean_dec(v_val_705_);
lean_inc(v___x_703_);
lean_inc(v_kind_698_);
lean_inc(v_fst_694_);
v___f_707_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 11, 3);
lean_closure_set(v___f_707_, 0, v_fst_694_);
lean_closure_set(v___f_707_, 1, v_kind_698_);
lean_closure_set(v___f_707_, 2, v___x_703_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_710_ = l_Lake_Job_bindM___redArg(v_outKind_706_, v_snd_689_, v___f_707_, v___x_708_, v___x_686_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_709_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v___x_703_);
lean_ctor_set(v___x_684_, 0, v_fst_694_);
v___x_712_ = v___x_684_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_fst_694_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_703_);
v___x_712_ = v_reuseFailAlloc_719_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v___x_710_);
lean_ctor_set(v___x_696_, 0, v___x_712_);
v___x_714_ = v___x_696_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_710_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_714_);
v___x_716_ = v___x_692_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_a_690_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec(v___x_704_);
lean_del_object(v___x_696_);
lean_dec(v_fst_694_);
lean_dec(v_snd_689_);
lean_del_object(v___x_684_);
lean_dec_ref(v_a_327_);
v___x_720_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_721_ = l_Lake_PartialBuildKey_toString(v_root_324_);
v___x_722_ = lean_string_append(v___x_720_, v___x_721_);
lean_dec_ref(v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
v___x_724_ = lean_string_append(v___x_722_, v___x_723_);
v___x_725_ = 1;
v___x_726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_703_, v___x_725_);
v___x_727_ = lean_string_append(v___x_724_, v___x_726_);
lean_dec_ref(v___x_726_);
v___x_728_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___x_730_ = 3;
v___x_731_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set_uint8(v___x_731_, sizeof(void*)*1, v___x_730_);
v___x_732_ = lean_array_get_size(v_a_690_);
v___x_733_ = lean_array_push(v_a_690_, v___x_731_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 1, v___x_733_);
lean_ctor_set(v___x_692_, 0, v___x_732_);
v___x_735_ = v___x_692_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_684_);
lean_dec(v_facet_682_);
lean_dec_ref(v_a_327_);
lean_dec_ref(v_root_324_);
return v___x_687_;
}
}
}
}
v___jp_334_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_337_, 0, v_a_335_);
lean_ctor_set(v___x_337_, 1, v_a_336_);
return v___x_337_;
}
v___jp_338_:
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v_a_339_);
lean_ctor_set(v___x_341_, 1, v_a_340_);
return v___x_341_;
}
v___jp_342_:
{
lean_object* v___x_345_; 
v___x_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_345_, 0, v_a_343_);
lean_ctor_set(v___x_345_, 1, v_a_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultPkg_323_ = stack[0].m_obj;
lean_object* v_root_324_ = stack[1].m_obj;
lean_object* v_self_325_ = stack[2].m_obj;
uint8_t v_facetless_326_ = stack[3].m_num;
lean_object* v_a_327_ = stack[4].m_obj;
lean_object* v_a_328_ = stack[5].m_obj;
lean_object* v_a_329_ = stack[6].m_obj;
lean_object* v_a_330_ = stack[7].m_obj;
lean_object* v_a_331_ = stack[8].m_obj;
lean_object* v_a_332_ = stack[9].m_obj;
lean_object* v_res_755_;
v_res_755_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_323_, v_root_324_, v_self_325_, v_facetless_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object* v_defaultPkg_756_, lean_object* v_root_757_, lean_object* v_self_758_, lean_object* v_facetless_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
uint8_t v_facetless_boxed_767_; lean_object* v_res_768_; 
v_facetless_boxed_767_ = lean_unbox(v_facetless_759_);
v_res_768_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_756_, v_root_757_, v_self_758_, v_facetless_boxed_767_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec(v_a_762_);
lean_dec(v_a_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(lean_object* v_00_u03b2_769_, lean_object* v_inst_770_, lean_object* v_t_771_, lean_object* v_k_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_771_, v_k_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(lean_object* v_00_u03b2_774_, lean_object* v_inst_775_, lean_object* v_t_776_, lean_object* v_k_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(v_00_u03b2_774_, v_inst_775_, v_t_776_, v_k_777_);
lean_dec(v_k_777_);
lean_dec(v_t_776_);
return v_res_778_;
}
}
lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object* v_defaultPkg_779_, lean_object* v_self_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
uint8_t v___x_788_; lean_object* v___x_789_; 
v___x_788_ = 1;
lean_inc_ref(v_self_780_);
v___x_789_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_779_, v_self_780_, v_self_780_, v___x_788_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
return v___x_789_;
}
}
LEAN_EXPORT void l_Lake_PartialBuildKey_fetchInCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultPkg_779_ = stack[0].m_obj;
lean_object* v_self_780_ = stack[1].m_obj;
lean_object* v_a_781_ = stack[2].m_obj;
lean_object* v_a_782_ = stack[3].m_obj;
lean_object* v_a_783_ = stack[4].m_obj;
lean_object* v_a_784_ = stack[5].m_obj;
lean_object* v_a_785_ = stack[6].m_obj;
lean_object* v_a_786_ = stack[7].m_obj;
lean_object* v_res_790_;
v_res_790_ = l_Lake_PartialBuildKey_fetchInCore(v_defaultPkg_779_, v_self_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
stack->m_obj
 = v_res_790_;
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore___boxed(lean_object* v_defaultPkg_791_, lean_object* v_self_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lake_PartialBuildKey_fetchInCore(v_defaultPkg_791_, v_self_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec(v_a_795_);
lean_dec(v_a_794_);
return v_res_800_;
}
}
lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object* v_defaultPkg_801_, lean_object* v_self_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
uint8_t v___x_810_; lean_object* v___x_811_; 
v___x_810_ = 1;
lean_inc_ref(v_self_802_);
v___x_811_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_801_, v_self_802_, v_self_802_, v___x_810_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_a_813_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v___x_811_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_snd_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v_snd_817_ = lean_ctor_get(v_a_812_, 1);
lean_inc(v_snd_817_);
lean_dec(v_a_812_);
v___x_818_ = l_Lake_Job_toOpaque___redArg(v_snd_817_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_a_813_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
lean_object* v_a_823_; lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_823_ = lean_ctor_get(v___x_811_, 0);
v_a_824_ = lean_ctor_get(v___x_811_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_811_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_inc(v_a_823_);
lean_dec(v___x_811_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_823_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_PartialBuildKey_fetchIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultPkg_801_ = stack[0].m_obj;
lean_object* v_self_802_ = stack[1].m_obj;
lean_object* v_a_803_ = stack[2].m_obj;
lean_object* v_a_804_ = stack[3].m_obj;
lean_object* v_a_805_ = stack[4].m_obj;
lean_object* v_a_806_ = stack[5].m_obj;
lean_object* v_a_807_ = stack[6].m_obj;
lean_object* v_a_808_ = stack[7].m_obj;
lean_object* v_res_832_;
v_res_832_ = l_Lake_PartialBuildKey_fetchIn(v_defaultPkg_801_, v_self_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn___boxed(lean_object* v_defaultPkg_833_, lean_object* v_self_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_PartialBuildKey_fetchIn(v_defaultPkg_833_, v_self_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
return v_res_842_;
}
}
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(lean_object* v_target_843_, lean_object* v_kind_844_, lean_object* v_facet_845_, lean_object* v_data_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_log_854_; uint8_t v_action_855_; uint8_t v_wantsRebuild_856_; uint8_t v_canceled_857_; lean_object* v_trace_858_; lean_object* v_buildTime_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_889_; 
v_log_854_ = lean_ctor_get(v___y_852_, 0);
v_action_855_ = lean_ctor_get_uint8(v___y_852_, sizeof(void*)*3);
v_wantsRebuild_856_ = lean_ctor_get_uint8(v___y_852_, sizeof(void*)*3 + 1);
v_canceled_857_ = lean_ctor_get_uint8(v___y_852_, sizeof(void*)*3 + 2);
v_trace_858_ = lean_ctor_get(v___y_852_, 1);
v_buildTime_859_ = lean_ctor_get(v___y_852_, 2);
v_isSharedCheck_889_ = !lean_is_exclusive(v___y_852_);
if (v_isSharedCheck_889_ == 0)
{
v___x_861_ = v___y_852_;
v_isShared_862_ = v_isSharedCheck_889_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_buildTime_859_);
lean_inc(v_trace_858_);
lean_inc(v_log_854_);
lean_dec(v___y_852_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_889_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_863_, 0, v_target_843_);
lean_ctor_set(v___x_863_, 1, v_kind_844_);
lean_ctor_set(v___x_863_, 2, v_data_846_);
lean_ctor_set(v___x_863_, 3, v_facet_845_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_850_);
lean_inc(v___y_849_);
lean_inc(v___y_848_);
v___x_864_ = lean_apply_7(v___y_847_, v___x_863_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v_log_854_, lean_box(0));
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_876_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_a_866_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_876_ == 0)
{
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_876_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_a_866_);
v___x_871_ = v___x_861_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_trace_858_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_buildTime_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*3, v_action_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*3 + 1, v_wantsRebuild_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_875_, sizeof(void*)*3 + 2, v_canceled_857_);
v___x_871_ = v_reuseFailAlloc_875_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_871_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_865_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_871_);
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
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_888_; 
v_a_877_ = lean_ctor_get(v___x_864_, 0);
v_a_878_ = lean_ctor_get(v___x_864_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_888_ == 0)
{
v___x_880_ = v___x_864_;
v_isShared_881_ = v_isSharedCheck_888_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_inc(v_a_877_);
lean_dec(v___x_864_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_888_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_a_878_);
v___x_883_ = v___x_861_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_878_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_trace_858_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_buildTime_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_887_, sizeof(void*)*3, v_action_855_);
lean_ctor_set_uint8(v_reuseFailAlloc_887_, sizeof(void*)*3 + 1, v_wantsRebuild_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_887_, sizeof(void*)*3 + 2, v_canceled_857_);
v___x_883_ = v_reuseFailAlloc_887_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_883_);
v___x_885_ = v___x_880_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_883_);
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
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_843_ = stack[0].m_obj;
lean_object* v_kind_844_ = stack[1].m_obj;
lean_object* v_facet_845_ = stack[2].m_obj;
lean_object* v_data_846_ = stack[3].m_obj;
lean_object* v___y_847_ = stack[4].m_obj;
lean_object* v___y_848_ = stack[5].m_obj;
lean_object* v___y_849_ = stack[6].m_obj;
lean_object* v___y_850_ = stack[7].m_obj;
lean_object* v___y_851_ = stack[8].m_obj;
lean_object* v___y_852_ = stack[9].m_obj;
lean_object* v_res_890_;
v_res_890_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(v_target_843_, v_kind_844_, v_facet_845_, v_data_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed(lean_object* v_target_891_, lean_object* v_kind_892_, lean_object* v_facet_893_, lean_object* v_data_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(v_target_891_, v_kind_892_, v_facet_893_, v_data_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec(v___y_897_);
lean_dec(v___y_896_);
return v_res_902_;
}
}
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(lean_object* v_root_903_, lean_object* v_self_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lake_instDataKindModule;
switch(lean_obj_tag(v_self_904_))
{
case 0:
{
lean_object* v_module_913_; lean_object* v_toContext_914_; lean_object* v___x_915_; 
lean_dec_ref(v_a_905_);
v_module_913_ = lean_ctor_get(v_self_904_, 0);
lean_inc_n(v_module_913_, 2);
lean_dec_ref_known(v_self_904_, 1);
v_toContext_914_ = lean_ctor_get(v_a_909_, 1);
v___x_915_ = l_Lake_Workspace_findModule_x3f(v_module_913_, v_toContext_914_);
if (lean_obj_tag(v___x_915_) == 1)
{
lean_object* v_val_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v_module_913_);
lean_dec_ref(v_root_903_);
v_val_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_val_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_918_ = 0;
v___x_919_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_val_916_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_task_pure(v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_912_);
lean_ctor_set(v___x_922_, 2, v___x_917_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*3, v___x_918_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_a_910_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v___x_915_);
v___x_924_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_925_ = l_Lake_BuildKey_toString(v_root_903_);
v___x_926_ = lean_string_append(v___x_924_, v___x_925_);
lean_dec_ref(v___x_925_);
v___x_927_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_928_ = lean_string_append(v___x_926_, v___x_927_);
v___x_929_ = 1;
v___x_930_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_913_, v___x_929_);
v___x_931_ = lean_string_append(v___x_928_, v___x_930_);
lean_dec_ref(v___x_930_);
v___x_932_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_933_ = lean_string_append(v___x_931_, v___x_932_);
v___x_934_ = 3;
v___x_935_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_934_);
v___x_936_ = lean_array_get_size(v_a_910_);
v___x_937_ = lean_array_push(v_a_910_, v___x_935_);
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
return v___x_938_;
}
}
case 1:
{
lean_object* v_toContext_939_; lean_object* v_package_940_; lean_object* v_packageMap_941_; lean_object* v___x_942_; 
lean_dec_ref(v_a_905_);
v_toContext_939_ = lean_ctor_get(v_a_909_, 1);
v_package_940_ = lean_ctor_get(v_self_904_, 0);
lean_inc(v_package_940_);
lean_dec_ref_known(v_self_904_, 1);
v_packageMap_941_ = lean_ctor_get(v_toContext_939_, 5);
v___x_942_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_941_, v_package_940_);
if (lean_obj_tag(v___x_942_) == 1)
{
lean_object* v_val_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_package_940_);
lean_dec_ref(v_root_903_);
v_val_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = l_Lake_instDataKindPackage;
v___x_945_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_946_ = 0;
v___x_947_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_val_943_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_task_pure(v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_944_);
lean_ctor_set(v___x_950_, 2, v___x_945_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*3, v___x_946_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v_a_910_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v___x_942_);
v___x_952_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_953_ = l_Lake_BuildKey_toString(v_root_903_);
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
lean_dec_ref(v___x_953_);
v___x_955_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
v___x_957_ = 1;
v___x_958_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_940_, v___x_957_);
v___x_959_ = lean_string_append(v___x_956_, v___x_958_);
lean_dec_ref(v___x_958_);
v___x_960_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
v___x_962_ = 3;
v___x_963_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*1, v___x_962_);
v___x_964_ = lean_array_get_size(v_a_910_);
v___x_965_ = lean_array_push(v_a_910_, v___x_963_);
v___x_966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
return v___x_966_;
}
}
case 2:
{
lean_object* v_toContext_967_; lean_object* v_package_968_; lean_object* v_module_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_a_905_);
v_toContext_967_ = lean_ctor_get(v_a_909_, 1);
v_package_968_ = lean_ctor_get(v_self_904_, 0);
v_module_969_ = lean_ctor_get(v_self_904_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_self_904_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_971_ = v_self_904_;
v_isShared_972_ = v_isSharedCheck_1027_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_module_969_);
lean_inc(v_package_968_);
lean_dec(v_self_904_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1027_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_packageMap_973_; lean_object* v___x_974_; 
v_packageMap_973_ = lean_ctor_get(v_toContext_967_, 5);
v___x_974_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_973_, v_package_968_);
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_976_; 
lean_dec(v_package_968_);
v_val_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc_n(v_val_975_, 2);
lean_dec_ref_known(v___x_974_, 1);
lean_inc(v_module_969_);
v___x_976_ = l_Lake_Package_findTargetModule_x3f(v_module_969_, v_val_975_);
if (lean_obj_tag(v___x_976_) == 1)
{
lean_object* v_val_977_; lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec(v_val_975_);
lean_dec(v_module_969_);
lean_dec_ref(v_root_903_);
v_val_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_979_ = 0;
v___x_980_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 0);
lean_ctor_set(v___x_971_, 1, v___x_980_);
lean_ctor_set(v___x_971_, 0, v_val_977_);
v___x_982_ = v___x_971_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_val_977_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v___x_980_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_task_pure(v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_912_);
lean_ctor_set(v___x_984_, 2, v___x_978_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*3, v___x_979_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v_a_910_);
return v___x_985_;
}
}
else
{
lean_object* v_baseName_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_dec(v___x_976_);
v_baseName_987_ = lean_ctor_get(v_val_975_, 1);
lean_inc(v_baseName_987_);
lean_dec(v_val_975_);
v___x_988_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_989_ = l_Lake_BuildKey_toString(v_root_903_);
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
lean_dec_ref(v___x_989_);
v___x_991_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
v___x_993_ = 1;
v___x_994_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_969_, v___x_993_);
v___x_995_ = lean_string_append(v___x_992_, v___x_994_);
lean_dec_ref(v___x_994_);
v___x_996_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
v___x_998_ = 0;
v___x_999_ = l_Lean_Name_toString(v_baseName_987_, v___x_998_);
v___x_1000_ = lean_string_append(v___x_997_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_1002_ = lean_string_append(v___x_1000_, v___x_1001_);
v___x_1003_ = 3;
v___x_1004_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set_uint8(v___x_1004_, sizeof(void*)*1, v___x_1003_);
v___x_1005_ = lean_array_get_size(v_a_910_);
v___x_1006_ = lean_array_push(v_a_910_, v___x_1004_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 1);
lean_ctor_set(v___x_971_, 1, v___x_1006_);
lean_ctor_set(v___x_971_, 0, v___x_1005_);
v___x_1008_ = v___x_971_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec(v___x_974_);
lean_dec(v_module_969_);
v___x_1010_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1011_ = l_Lake_BuildKey_toString(v_root_903_);
v___x_1012_ = lean_string_append(v___x_1010_, v___x_1011_);
lean_dec_ref(v___x_1011_);
v___x_1013_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
v___x_1015_ = 1;
v___x_1016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_968_, v___x_1015_);
v___x_1017_ = lean_string_append(v___x_1014_, v___x_1016_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_1019_ = lean_string_append(v___x_1017_, v___x_1018_);
v___x_1020_ = 3;
v___x_1021_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set_uint8(v___x_1021_, sizeof(void*)*1, v___x_1020_);
v___x_1022_ = lean_array_get_size(v_a_910_);
v___x_1023_ = lean_array_push(v_a_910_, v___x_1021_);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 1);
lean_ctor_set(v___x_971_, 1, v___x_1023_);
lean_ctor_set(v___x_971_, 0, v___x_1022_);
v___x_1025_ = v___x_971_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
case 3:
{
lean_object* v_toContext_1028_; lean_object* v_package_1029_; lean_object* v_target_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1058_; 
v_toContext_1028_ = lean_ctor_get(v_a_909_, 1);
v_package_1029_ = lean_ctor_get(v_self_904_, 0);
v_target_1030_ = lean_ctor_get(v_self_904_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_self_904_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1032_ = v_self_904_;
v_isShared_1033_ = v_isSharedCheck_1058_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_target_1030_);
lean_inc(v_package_1029_);
lean_dec(v_self_904_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1058_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_packageMap_1034_; lean_object* v___x_1035_; 
v_packageMap_1034_ = lean_ctor_get(v_toContext_1028_, 5);
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_1034_, v_package_1029_);
if (lean_obj_tag(v___x_1035_) == 1)
{
lean_object* v_val_1036_; lean_object* v___x_1038_; 
lean_dec(v_package_1029_);
lean_dec_ref(v_root_903_);
v_val_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v___x_1035_, 1);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
lean_ctor_set(v___x_1032_, 0, v_val_1036_);
v___x_1038_ = v___x_1032_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_val_1036_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_target_1030_);
v___x_1038_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; 
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc(v_a_907_);
lean_inc(v_a_906_);
v___x_1039_ = lean_apply_7(v_a_905_, v___x_1038_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, lean_box(0));
return v___x_1039_;
}
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_dec(v___x_1035_);
lean_dec(v_target_1030_);
lean_dec_ref(v_a_905_);
v___x_1041_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1042_ = l_Lake_BuildKey_toString(v_root_903_);
v___x_1043_ = lean_string_append(v___x_1041_, v___x_1042_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
v___x_1046_ = 1;
v___x_1047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_1029_, v___x_1046_);
v___x_1048_ = lean_string_append(v___x_1045_, v___x_1047_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_1050_ = lean_string_append(v___x_1048_, v___x_1049_);
v___x_1051_ = 3;
v___x_1052_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set_uint8(v___x_1052_, sizeof(void*)*1, v___x_1051_);
v___x_1053_ = lean_array_get_size(v_a_910_);
v___x_1054_ = lean_array_push(v_a_910_, v___x_1052_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 1);
lean_ctor_set(v___x_1032_, 1, v___x_1054_);
lean_ctor_set(v___x_1032_, 0, v___x_1053_);
v___x_1056_ = v___x_1032_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
default: 
{
lean_object* v_target_1059_; lean_object* v_facet_1060_; lean_object* v___x_1061_; 
v_target_1059_ = lean_ctor_get(v_self_904_, 0);
v_facet_1060_ = lean_ctor_get(v_self_904_, 1);
lean_inc_ref(v_a_905_);
lean_inc_ref(v_target_1059_);
lean_inc_ref(v_root_903_);
v___x_1061_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_root_903_, v_target_1059_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1110_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_a_1063_ = lean_ctor_get(v___x_1061_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1065_ = v___x_1061_;
v_isShared_1066_ = v_isSharedCheck_1110_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1110_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_kind_1067_; uint8_t v___x_1068_; 
v_kind_1067_ = lean_ctor_get(v_a_1062_, 1);
v___x_1068_ = l_Lean_Name_isAnonymous(v_kind_1067_);
if (v___x_1068_ == 0)
{
lean_object* v_toContext_1069_; lean_object* v_facetConfigs_1070_; lean_object* v___x_1071_; 
lean_inc(v_facet_1060_);
lean_inc_ref(v_target_1059_);
lean_dec_ref_known(v_self_904_, 2);
v_toContext_1069_ = lean_ctor_get(v_a_909_, 1);
v_facetConfigs_1070_ = lean_ctor_get(v_toContext_1069_, 6);
v___x_1071_ = l_Lake_FacetConfigMap_get_x3f(v_facet_1060_, v_facetConfigs_1070_);
if (lean_obj_tag(v___x_1071_) == 1)
{
lean_object* v_val_1072_; lean_object* v_outKind_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec_ref(v_root_903_);
v_val_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_outKind_1073_ = lean_ctor_get(v_val_1072_, 2);
lean_inc(v_outKind_1073_);
lean_dec(v_val_1072_);
lean_inc(v_kind_1067_);
v___f_1074_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed), 11, 3);
lean_closure_set(v___f_1074_, 0, v_target_1059_);
lean_closure_set(v___f_1074_, 1, v_kind_1067_);
lean_closure_set(v___f_1074_, 2, v_facet_1060_);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_1077_ = l_Lake_Job_bindM___redArg(v_outKind_1073_, v_a_1062_, v___f_1074_, v___x_1075_, v___x_1068_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v___x_1076_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1077_);
v___x_1079_ = v___x_1065_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_a_1063_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_dec(v___x_1071_);
lean_dec(v_a_1062_);
lean_dec_ref(v_target_1059_);
lean_dec_ref(v_a_905_);
v___x_1081_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1082_ = l_Lake_BuildKey_toString(v_root_903_);
v___x_1083_ = lean_string_append(v___x_1081_, v___x_1082_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
v___x_1085_ = lean_string_append(v___x_1083_, v___x_1084_);
v___x_1086_ = 1;
v___x_1087_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_1060_, v___x_1086_);
v___x_1088_ = lean_string_append(v___x_1085_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v___x_1089_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_1090_ = lean_string_append(v___x_1088_, v___x_1089_);
v___x_1091_ = 3;
v___x_1092_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*1, v___x_1091_);
v___x_1093_ = lean_array_get_size(v_a_1063_);
v___x_1094_ = lean_array_push(v_a_1063_, v___x_1092_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 1);
lean_ctor_set(v___x_1065_, 1, v___x_1094_);
lean_ctor_set(v___x_1065_, 0, v___x_1093_);
v___x_1096_ = v___x_1065_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec(v_a_1062_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_root_903_);
v___x_1098_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1099_ = l_Lake_BuildKey_toString(v_self_904_);
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
v___x_1102_ = lean_string_append(v___x_1100_, v___x_1101_);
v___x_1103_ = 3;
v___x_1104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*1, v___x_1103_);
v___x_1105_ = lean_array_get_size(v_a_1063_);
v___x_1106_ = lean_array_push(v_a_1063_, v___x_1104_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 1);
lean_ctor_set(v___x_1065_, 1, v___x_1106_);
lean_ctor_set(v___x_1065_, 0, v___x_1105_);
v___x_1108_ = v___x_1065_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_dec_ref_known(v_self_904_, 2);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_root_903_);
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_903_ = stack[0].m_obj;
lean_object* v_self_904_ = stack[1].m_obj;
lean_object* v_a_905_ = stack[2].m_obj;
lean_object* v_a_906_ = stack[3].m_obj;
lean_object* v_a_907_ = stack[4].m_obj;
lean_object* v_a_908_ = stack[5].m_obj;
lean_object* v_a_909_ = stack[6].m_obj;
lean_object* v_a_910_ = stack[7].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_root_903_, v_self_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___boxed(lean_object* v_root_1112_, lean_object* v_self_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_root_1112_, v_self_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec(v_a_1115_);
return v_res_1121_;
}
}
lean_object* l_Lake_BuildKey_fetch___redArg(lean_object* v_self_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; 
lean_inc_ref(v_self_1122_);
v___x_1130_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_self_1122_, v_self_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT void l_Lake_BuildKey_fetch___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1122_ = stack[0].m_obj;
lean_object* v_a_1123_ = stack[1].m_obj;
lean_object* v_a_1124_ = stack[2].m_obj;
lean_object* v_a_1125_ = stack[3].m_obj;
lean_object* v_a_1126_ = stack[4].m_obj;
lean_object* v_a_1127_ = stack[5].m_obj;
lean_object* v_a_1128_ = stack[6].m_obj;
lean_object* v_res_1131_;
v_res_1131_ = l_Lake_BuildKey_fetch___redArg(v_self_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
stack->m_obj
 = v_res_1131_;
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg___boxed(lean_object* v_self_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lake_BuildKey_fetch___redArg(v_self_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec(v_a_1134_);
return v_res_1140_;
}
}
lean_object* l_Lake_BuildKey_fetch(lean_object* v_00_u03b1_1141_, lean_object* v_self_1142_, lean_object* v_inst_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1151_; 
lean_inc_ref(v_self_1142_);
v___x_1151_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_self_1142_, v_self_1142_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT void l_Lake_BuildKey_fetch_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1142_ = stack[1].m_obj;
lean_object* v_a_1144_ = stack[3].m_obj;
lean_object* v_a_1145_ = stack[4].m_obj;
lean_object* v_a_1146_ = stack[5].m_obj;
lean_object* v_a_1147_ = stack[6].m_obj;
lean_object* v_a_1148_ = stack[7].m_obj;
lean_object* v_a_1149_ = stack[8].m_obj;
lean_object* v_res_1152_;
v_res_1152_ = l_Lake_BuildKey_fetch(lean_box(0), v_self_1142_, lean_box(0), v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
stack->m_obj
 = v_res_1152_;
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___boxed(lean_object* v_00_u03b1_1153_, lean_object* v_self_1154_, lean_object* v_inst_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lake_BuildKey_fetch(v_00_u03b1_1153_, v_self_1154_, v_inst_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec(v_a_1157_);
return v_res_1163_;
}
}
lean_object* l_Lake_Target_fetchIn___redArg(lean_object* v_inst_1168_, lean_object* v_defaultPkg_1169_, lean_object* v_self_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
uint8_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = 1;
lean_inc_ref_n(v_self_1170_, 2);
v___x_1179_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1169_, v_self_1170_, v_self_1170_, v___x_1178_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1221_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_a_1181_ = lean_ctor_get(v___x_1179_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1183_ = v___x_1179_;
v_isShared_1184_ = v_isSharedCheck_1221_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1221_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___y_1186_; lean_object* v_snd_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1219_; 
v_snd_1204_ = lean_ctor_get(v_a_1180_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; 
v_unused_1220_ = lean_ctor_get(v_a_1180_, 0);
lean_dec(v_unused_1220_);
v___x_1206_ = v_a_1180_;
v_isShared_1207_ = v_isSharedCheck_1219_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_snd_1204_);
lean_dec(v_a_1180_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1219_;
goto v_resetjp_1205_;
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1187_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__0));
v___x_1188_ = l_Lake_PartialBuildKey_toString(v_self_1170_);
v___x_1189_ = lean_string_append(v___x_1187_, v___x_1188_);
lean_dec_ref(v___x_1188_);
v___x_1190_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__1));
v___x_1191_ = lean_string_append(v___x_1189_, v___x_1190_);
v___x_1192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1168_, v___x_1178_);
v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
lean_dec_ref(v___x_1192_);
v___x_1194_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__2));
v___x_1195_ = lean_string_append(v___x_1193_, v___x_1194_);
v___x_1196_ = lean_string_append(v___x_1195_, v___y_1186_);
lean_dec_ref(v___y_1186_);
v___x_1197_ = 3;
v___x_1198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*1, v___x_1197_);
v___x_1199_ = lean_array_get_size(v_a_1181_);
v___x_1200_ = lean_array_push(v_a_1181_, v___x_1198_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set_tag(v___x_1183_, 1);
lean_ctor_set(v___x_1183_, 1, v___x_1200_);
lean_ctor_set(v___x_1183_, 0, v___x_1199_);
v___x_1202_ = v___x_1183_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
v_resetjp_1205_:
{
lean_object* v_kind_1208_; uint8_t v___x_1209_; 
v_kind_1208_ = lean_ctor_get(v_snd_1204_, 1);
v___x_1209_ = lean_name_eq(v_kind_1208_, v_inst_1168_);
if (v___x_1209_ == 0)
{
uint8_t v___x_1210_; 
lean_inc(v_kind_1208_);
lean_del_object(v___x_1206_);
lean_dec(v_snd_1204_);
v___x_1210_ = l_Lean_Name_isAnonymous(v_kind_1208_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_1212_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1208_, v___x_1178_);
v___x_1213_ = lean_string_append(v___x_1211_, v___x_1212_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_string_append(v___x_1213_, v___x_1211_);
v___y_1186_ = v___x_1214_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1215_; 
lean_dec(v_kind_1208_);
v___x_1215_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__3));
v___y_1186_ = v___x_1215_;
goto v___jp_1185_;
}
}
else
{
lean_object* v___x_1217_; 
lean_del_object(v___x_1183_);
lean_dec_ref(v_self_1170_);
lean_dec(v_inst_1168_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v_a_1181_);
lean_ctor_set(v___x_1206_, 0, v_snd_1204_);
v___x_1217_ = v___x_1206_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_snd_1204_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_a_1181_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_self_1170_);
lean_dec(v_inst_1168_);
v_a_1222_ = lean_ctor_get(v___x_1179_, 0);
v_a_1223_ = lean_ctor_get(v___x_1179_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1179_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_inc(v_a_1222_);
lean_dec(v___x_1179_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1222_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Target_fetchIn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1168_ = stack[0].m_obj;
lean_object* v_defaultPkg_1169_ = stack[1].m_obj;
lean_object* v_self_1170_ = stack[2].m_obj;
lean_object* v_a_1171_ = stack[3].m_obj;
lean_object* v_a_1172_ = stack[4].m_obj;
lean_object* v_a_1173_ = stack[5].m_obj;
lean_object* v_a_1174_ = stack[6].m_obj;
lean_object* v_a_1175_ = stack[7].m_obj;
lean_object* v_a_1176_ = stack[8].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l_Lake_Target_fetchIn___redArg(v_inst_1168_, v_defaultPkg_1169_, v_self_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg___boxed(lean_object* v_inst_1232_, lean_object* v_defaultPkg_1233_, lean_object* v_self_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lake_Target_fetchIn___redArg(v_inst_1232_, v_defaultPkg_1233_, v_self_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec(v_a_1236_);
return v_res_1242_;
}
}
lean_object* l_Lake_Target_fetchIn(lean_object* v_00_u03b1_1243_, lean_object* v_inst_1244_, lean_object* v_defaultPkg_1245_, lean_object* v_self_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lake_Target_fetchIn___redArg(v_inst_1244_, v_defaultPkg_1245_, v_self_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT void l_Lake_Target_fetchIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1244_ = stack[1].m_obj;
lean_object* v_defaultPkg_1245_ = stack[2].m_obj;
lean_object* v_self_1246_ = stack[3].m_obj;
lean_object* v_a_1247_ = stack[4].m_obj;
lean_object* v_a_1248_ = stack[5].m_obj;
lean_object* v_a_1249_ = stack[6].m_obj;
lean_object* v_a_1250_ = stack[7].m_obj;
lean_object* v_a_1251_ = stack[8].m_obj;
lean_object* v_a_1252_ = stack[9].m_obj;
lean_object* v_res_1255_;
v_res_1255_ = l_Lake_Target_fetchIn(lean_box(0), v_inst_1244_, v_defaultPkg_1245_, v_self_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
stack->m_obj
 = v_res_1255_;
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_inst_1257_, lean_object* v_defaultPkg_1258_, lean_object* v_self_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lake_Target_fetchIn(v_00_u03b1_1256_, v_inst_1257_, v_defaultPkg_1258_, v_self_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec(v_a_1261_);
return v_res_1267_;
}
}
lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0(lean_object* v_inst_1268_, lean_object* v_defaultPkg_1269_, lean_object* v_x_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lake_Target_fetchIn___redArg(v_inst_1268_, v_defaultPkg_1269_, v_x_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT void l_Lake_TargetArray_fetchIn___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1268_ = stack[0].m_obj;
lean_object* v_defaultPkg_1269_ = stack[1].m_obj;
lean_object* v_x_1270_ = stack[2].m_obj;
lean_object* v___y_1271_ = stack[3].m_obj;
lean_object* v___y_1272_ = stack[4].m_obj;
lean_object* v___y_1273_ = stack[5].m_obj;
lean_object* v___y_1274_ = stack[6].m_obj;
lean_object* v___y_1275_ = stack[7].m_obj;
lean_object* v___y_1276_ = stack[8].m_obj;
lean_object* v_res_1279_;
v_res_1279_ = l_Lake_TargetArray_fetchIn___redArg___lam__0(v_inst_1268_, v_defaultPkg_1269_, v_x_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
stack->m_obj
 = v_res_1279_;
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed(lean_object* v_inst_1280_, lean_object* v_defaultPkg_1281_, lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lake_TargetArray_fetchIn___redArg___lam__0(v_inst_1280_, v_defaultPkg_1281_, v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec(v___y_1284_);
return v_res_1290_;
}
}
lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object* v_inst_1291_, lean_object* v_defaultPkg_1292_, lean_object* v_self_1293_, lean_object* v_traceCaption_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v_toApplicative_1303_; lean_object* v_toBind_1304_; lean_object* v_toFunctor_1305_; lean_object* v_toPure_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___f_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_521__overap_1323_; lean_object* v___x_1324_; 
v___x_1302_ = l_instMonadBaseIO;
v_toApplicative_1303_ = lean_ctor_get(v___x_1302_, 0);
v_toBind_1304_ = lean_ctor_get(v___x_1302_, 1);
v_toFunctor_1305_ = lean_ctor_get(v_toApplicative_1303_, 0);
v_toPure_1306_ = lean_ctor_get(v_toApplicative_1303_, 1);
v___f_1307_ = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1307_, 0, v_inst_1291_);
lean_closure_set(v___f_1307_, 1, v_defaultPkg_1292_);
lean_inc_n(v_toBind_1304_, 3);
lean_inc_n(v_toPure_1306_, 5);
v___f_1308_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1308_, 0, v_toPure_1306_);
lean_closure_set(v___f_1308_, 1, v_toBind_1304_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1309_, 0, v_toPure_1306_);
lean_closure_set(v___f_1309_, 1, v_toBind_1304_);
lean_inc_ref(v___f_1308_);
v___f_1310_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1310_, 0, v_toPure_1306_);
lean_closure_set(v___f_1310_, 1, v___f_1308_);
lean_inc_ref_n(v_toFunctor_1305_, 2);
v___f_1311_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1311_, 0, v_toFunctor_1305_);
lean_closure_set(v___f_1311_, 1, v_toPure_1306_);
lean_closure_set(v___f_1311_, 2, v_toBind_1304_);
v___x_1312_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1305_);
v___f_1313_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1313_, 0, v_toPure_1306_);
v___x_1314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___f_1313_);
lean_ctor_set(v___x_1314_, 2, v___f_1311_);
lean_ctor_set(v___x_1314_, 3, v___f_1310_);
lean_ctor_set(v___x_1314_, 4, v___f_1309_);
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v___f_1308_);
v___x_1316_ = l_ReaderT_instMonad___redArg(v___x_1315_);
v___x_1317_ = l_StateRefT_x27_instMonad___redArg(v___x_1316_);
v___x_1318_ = l_ReaderT_instMonad___redArg(v___x_1317_);
v___x_1319_ = l_ReaderT_instMonad___redArg(v___x_1318_);
v___x_1320_ = l_Lake_EquipT_instMonad___redArg(v___x_1319_);
v_sz_1321_ = lean_array_size(v_self_1293_);
v___x_1322_ = ((size_t)0ULL);
v___x_521__overap_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1320_, v___f_1307_, v_sz_1321_, v___x_1322_, v_self_1293_);
lean_inc_ref(v_a_1299_);
lean_inc(v_a_1298_);
lean_inc(v_a_1297_);
lean_inc(v_a_1296_);
v___x_1324_ = lean_apply_7(v___x_521__overap_1323_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, lean_box(0));
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_a_1326_ = lean_ctor_get(v___x_1324_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v___x_1324_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = l_Lake_Job_collectArray___redArg(v_a_1325_, v_traceCaption_1294_);
lean_dec(v_a_1325_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_a_1326_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_traceCaption_1294_);
v_a_1335_ = lean_ctor_get(v___x_1324_, 0);
v_a_1336_ = lean_ctor_get(v___x_1324_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1324_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_inc(v_a_1335_);
lean_dec(v___x_1324_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1335_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_TargetArray_fetchIn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1291_ = stack[0].m_obj;
lean_object* v_defaultPkg_1292_ = stack[1].m_obj;
lean_object* v_self_1293_ = stack[2].m_obj;
lean_object* v_traceCaption_1294_ = stack[3].m_obj;
lean_object* v_a_1295_ = stack[4].m_obj;
lean_object* v_a_1296_ = stack[5].m_obj;
lean_object* v_a_1297_ = stack[6].m_obj;
lean_object* v_a_1298_ = stack[7].m_obj;
lean_object* v_a_1299_ = stack[8].m_obj;
lean_object* v_a_1300_ = stack[9].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = l_Lake_TargetArray_fetchIn___redArg(v_inst_1291_, v_defaultPkg_1292_, v_self_1293_, v_traceCaption_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
stack->m_obj
 = v_res_1344_;
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___boxed(lean_object* v_inst_1345_, lean_object* v_defaultPkg_1346_, lean_object* v_self_1347_, lean_object* v_traceCaption_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lake_TargetArray_fetchIn___redArg(v_inst_1345_, v_defaultPkg_1346_, v_self_1347_, v_traceCaption_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1356_;
}
}
lean_object* l_Lake_TargetArray_fetchIn(lean_object* v_00_u03b1_1357_, lean_object* v_inst_1358_, lean_object* v_defaultPkg_1359_, lean_object* v_self_1360_, lean_object* v_traceCaption_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lake_TargetArray_fetchIn___redArg(v_inst_1358_, v_defaultPkg_1359_, v_self_1360_, v_traceCaption_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT void l_Lake_TargetArray_fetchIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1358_ = stack[1].m_obj;
lean_object* v_defaultPkg_1359_ = stack[2].m_obj;
lean_object* v_self_1360_ = stack[3].m_obj;
lean_object* v_traceCaption_1361_ = stack[4].m_obj;
lean_object* v_a_1362_ = stack[5].m_obj;
lean_object* v_a_1363_ = stack[6].m_obj;
lean_object* v_a_1364_ = stack[7].m_obj;
lean_object* v_a_1365_ = stack[8].m_obj;
lean_object* v_a_1366_ = stack[9].m_obj;
lean_object* v_a_1367_ = stack[10].m_obj;
lean_object* v_res_1370_;
v_res_1370_ = l_Lake_TargetArray_fetchIn(lean_box(0), v_inst_1358_, v_defaultPkg_1359_, v_self_1360_, v_traceCaption_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
stack->m_obj
 = v_res_1370_;
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___boxed(lean_object* v_00_u03b1_1371_, lean_object* v_inst_1372_, lean_object* v_defaultPkg_1373_, lean_object* v_self_1374_, lean_object* v_traceCaption_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lake_TargetArray_fetchIn(v_00_u03b1_1371_, v_inst_1372_, v_defaultPkg_1373_, v_self_1374_, v_traceCaption_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec(v_a_1377_);
return v_res_1383_;
}
}
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Key(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Target_Fetch(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Key(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Target_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Target_Fetch(builtin);
}
#ifdef __cplusplus
}
#endif
