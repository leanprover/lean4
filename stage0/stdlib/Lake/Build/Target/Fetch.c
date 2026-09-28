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
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(lean_object* v_defaultPkg_47_, lean_object* v_root_48_, lean_object* v_name_49_, lean_object* v_a_50_, lean_object* v_a_51_){
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___boxed(lean_object* v_defaultPkg_112_, lean_object* v_root_113_, lean_object* v_name_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(v_defaultPkg_112_, v_root_113_, v_name_114_, v_a_115_, v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(lean_object* v_defaultPkg_119_, lean_object* v_root_120_, lean_object* v_name_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_a_130_; 
switch(lean_obj_tag(v_name_121_))
{
case 0:
{
lean_object* v___x_146_; 
lean_dec_ref(v_root_120_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_defaultPkg_119_);
lean_ctor_set(v___x_146_, 1, v_a_127_);
return v___x_146_;
}
case 2:
{
lean_object* v_toContext_147_; lean_object* v_packageMap_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec_ref(v_defaultPkg_119_);
v_toContext_147_ = lean_ctor_get(v_a_126_, 1);
v_packageMap_148_ = lean_ctor_get(v_toContext_147_, 5);
v___x_149_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(v_name_121_);
lean_inc(v_packageMap_148_);
v___x_150_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_149_, v_packageMap_148_, v_name_121_);
if (lean_obj_tag(v___x_150_) == 1)
{
lean_object* v_val_151_; lean_object* v___x_152_; 
lean_dec_ref_known(v_name_121_, 2);
lean_dec_ref(v_root_120_);
v_val_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_val_151_);
lean_ctor_set(v___x_152_, 1, v_a_127_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v___x_150_);
v___x_153_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_154_ = l_Lake_PartialBuildKey_toString(v_root_120_);
v___x_155_ = lean_string_append(v___x_153_, v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
v___x_158_ = 1;
v___x_159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_121_, v___x_158_);
v___x_160_ = lean_string_append(v___x_157_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_161_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_162_ = lean_string_append(v___x_160_, v___x_161_);
v___x_163_ = 3;
v___x_164_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*1, v___x_163_);
v___x_165_ = lean_array_get_size(v_a_127_);
v___x_166_ = lean_array_push(v_a_127_, v___x_164_);
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
return v___x_167_;
}
}
default: 
{
lean_object* v_toContext_168_; lean_object* v_packages_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___f_173_; size_t v_sz_174_; size_t v___x_175_; lean_object* v___x_176_; lean_object* v_fst_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v_defaultPkg_119_);
v_toContext_168_ = lean_ctor_get(v_a_126_, 1);
v_packages_169_ = lean_ctor_get(v_toContext_168_, 4);
v___x_170_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13));
v___x_171_ = lean_box(0);
v___x_172_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
lean_inc(v_name_121_);
v___f_173_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_173_, 0, v_name_121_);
lean_closure_set(v___f_173_, 1, v___x_172_);
lean_closure_set(v___f_173_, 2, v___x_171_);
v_sz_174_ = lean_array_size(v_packages_169_);
v___x_175_ = ((size_t)0ULL);
lean_inc_ref(v_packages_169_);
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_170_, v_packages_169_, v___f_173_, v_sz_174_, v___x_175_, v___x_172_);
v_fst_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v___x_176_, 1);
lean_dec(v_unused_187_);
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_186_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_fst_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_186_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
if (lean_obj_tag(v_fst_177_) == 0)
{
lean_del_object(v___x_179_);
v_a_130_ = v_a_127_;
goto v___jp_129_;
}
else
{
lean_object* v_val_181_; 
v_val_181_ = lean_ctor_get(v_fst_177_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v_fst_177_, 1);
if (lean_obj_tag(v_val_181_) == 1)
{
lean_object* v_val_182_; lean_object* v___x_184_; 
lean_dec(v_name_121_);
lean_dec_ref(v_root_120_);
v_val_182_ = lean_ctor_get(v_val_181_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v_val_181_, 1);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 1, v_a_127_);
lean_ctor_set(v___x_179_, 0, v_val_182_);
v___x_184_ = v___x_179_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_val_182_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_a_127_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_dec(v_val_181_);
lean_del_object(v___x_179_);
v_a_130_ = v_a_127_;
goto v___jp_129_;
}
}
}
}
}
v___jp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_131_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_132_ = l_Lake_PartialBuildKey_toString(v_root_120_);
v___x_133_ = lean_string_append(v___x_131_, v___x_132_);
lean_dec_ref(v___x_132_);
v___x_134_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_135_ = lean_string_append(v___x_133_, v___x_134_);
v___x_136_ = 1;
v___x_137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_121_, v___x_136_);
v___x_138_ = lean_string_append(v___x_135_, v___x_137_);
lean_dec_ref(v___x_137_);
v___x_139_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_140_ = lean_string_append(v___x_138_, v___x_139_);
v___x_141_ = 3;
v___x_142_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = lean_array_get_size(v_a_130_);
v___x_144_ = lean_array_push(v_a_130_, v___x_142_);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(lean_object* v_defaultPkg_188_, lean_object* v_root_189_, lean_object* v_name_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(v_defaultPkg_188_, v_root_189_, v_name_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(lean_object* v_target_199_, lean_object* v_kind_200_, lean_object* v___x_201_, lean_object* v_data_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_log_210_; uint8_t v_action_211_; uint8_t v_wantsRebuild_212_; uint8_t v_canceled_213_; lean_object* v_trace_214_; lean_object* v_buildTime_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_245_; 
v_log_210_ = lean_ctor_get(v___y_208_, 0);
v_action_211_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*3);
v_wantsRebuild_212_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*3 + 1);
v_canceled_213_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*3 + 2);
v_trace_214_ = lean_ctor_get(v___y_208_, 1);
v_buildTime_215_ = lean_ctor_get(v___y_208_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v___y_208_);
if (v_isSharedCheck_245_ == 0)
{
v___x_217_ = v___y_208_;
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_buildTime_215_);
lean_inc(v_trace_214_);
lean_inc(v_log_210_);
lean_dec(v___y_208_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_245_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_219_, 0, v_target_199_);
lean_ctor_set(v___x_219_, 1, v_kind_200_);
lean_ctor_set(v___x_219_, 2, v_data_202_);
lean_ctor_set(v___x_219_, 3, v___x_201_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc(v___y_205_);
lean_inc(v___y_204_);
v___x_220_ = lean_apply_7(v___y_203_, v___x_219_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v_log_210_, lean_box(0));
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_232_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_a_222_ = lean_ctor_get(v___x_220_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_232_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v_a_222_);
v___x_227_ = v___x_217_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_222_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_trace_214_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_buildTime_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*3, v_action_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*3 + 1, v_wantsRebuild_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*3 + 2, v_canceled_213_);
v___x_227_ = v_reuseFailAlloc_231_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_227_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_221_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v_a_233_ = lean_ctor_get(v___x_220_, 0);
v_a_234_ = lean_ctor_get(v___x_220_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v___x_220_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_inc(v_a_233_);
lean_dec(v___x_220_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v_a_234_);
v___x_239_ = v___x_217_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_trace_214_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_buildTime_215_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3, v_action_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3 + 1, v_wantsRebuild_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*3 + 2, v_canceled_213_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object* v_target_246_, lean_object* v_kind_247_, lean_object* v___x_248_, lean_object* v_data_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(v_target_246_, v_kind_247_, v___x_248_, v_data_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec(v___y_252_);
lean_dec(v___y_251_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(lean_object* v_t_258_, lean_object* v_k_259_){
_start:
{
if (lean_obj_tag(v_t_258_) == 0)
{
lean_object* v_k_260_; lean_object* v_v_261_; lean_object* v_l_262_; lean_object* v_r_263_; uint8_t v___x_264_; 
v_k_260_ = lean_ctor_get(v_t_258_, 1);
v_v_261_ = lean_ctor_get(v_t_258_, 2);
v_l_262_ = lean_ctor_get(v_t_258_, 3);
v_r_263_ = lean_ctor_get(v_t_258_, 4);
v___x_264_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_259_, v_k_260_);
switch(v___x_264_)
{
case 0:
{
v_t_258_ = v_l_262_;
goto _start;
}
case 1:
{
lean_object* v___x_266_; 
lean_inc(v_v_261_);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v_v_261_);
return v___x_266_;
}
default: 
{
v_t_258_ = v_r_263_;
goto _start;
}
}
}
else
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(lean_object* v_t_269_, lean_object* v_k_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_269_, v_k_270_);
lean_dec(v_k_270_);
lean_dec(v_t_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(lean_object* v_package_272_, lean_object* v_as_273_, size_t v_sz_274_, size_t v_i_275_, lean_object* v_b_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = lean_usize_dec_lt(v_i_275_, v_sz_274_);
if (v___x_277_ == 0)
{
lean_inc_ref(v_b_276_);
return v_b_276_;
}
else
{
lean_object* v_a_278_; lean_object* v_baseName_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_a_278_ = lean_array_uget_borrowed(v_as_273_, v_i_275_);
v_baseName_279_ = lean_ctor_get(v_a_278_, 1);
v___x_280_ = lean_box(0);
v___x_281_ = lean_name_eq(v_baseName_279_, v_package_272_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; size_t v___x_283_; size_t v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_add(v_i_275_, v___x_283_);
v_i_275_ = v___x_284_;
v_b_276_ = v___x_282_;
goto _start;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_inc(v_a_278_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_a_278_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_280_);
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(lean_object* v_package_289_, lean_object* v_as_290_, lean_object* v_sz_291_, lean_object* v_i_292_, lean_object* v_b_293_){
_start:
{
size_t v_sz_boxed_294_; size_t v_i_boxed_295_; lean_object* v_res_296_; 
v_sz_boxed_294_ = lean_unbox_usize(v_sz_291_);
lean_dec(v_sz_291_);
v_i_boxed_295_ = lean_unbox_usize(v_i_292_);
lean_dec(v_i_292_);
v_res_296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_289_, v_as_290_, v_sz_boxed_294_, v_i_boxed_295_, v_b_293_);
lean_dec_ref(v_b_293_);
lean_dec_ref(v_as_290_);
lean_dec(v_package_289_);
return v_res_296_;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2));
v___x_302_ = l_Lake_BuildTrace_nil(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_305_ = 0;
v___x_306_ = 0;
v___x_307_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0));
v___x_308_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_304_);
lean_ctor_set(v___x_308_, 2, v___x_303_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*3, v___x_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*3 + 1, v___x_305_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*3 + 2, v___x_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object* v_defaultPkg_319_, lean_object* v_root_320_, lean_object* v_self_321_, uint8_t v_facetless_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v_a_335_; lean_object* v_a_336_; lean_object* v_a_339_; lean_object* v_a_340_; lean_object* v___x_342_; 
v___x_342_ = l_Lake_instDataKindModule;
switch(lean_obj_tag(v_self_321_))
{
case 0:
{
lean_object* v_module_343_; lean_object* v_toContext_344_; lean_object* v___x_345_; 
lean_dec_ref(v_a_323_);
lean_dec_ref(v_defaultPkg_319_);
v_module_343_ = lean_ctor_get(v_self_321_, 0);
lean_inc_n(v_module_343_, 2);
lean_dec_ref_known(v_self_321_, 1);
v_toContext_344_ = lean_ctor_get(v_a_327_, 1);
v___x_345_ = l_Lake_Workspace_findModule_x3f(v_module_343_, v_toContext_344_);
if (lean_obj_tag(v___x_345_) == 1)
{
lean_object* v_val_346_; lean_object* v_lib_347_; lean_object* v_pkg_348_; lean_object* v_keyName_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec_ref(v_root_320_);
v_val_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v___x_345_, 1);
v_lib_347_ = lean_ctor_get(v_val_346_, 0);
v_pkg_348_ = lean_ctor_get(v_lib_347_, 0);
v_keyName_349_ = lean_ctor_get(v_pkg_348_, 2);
lean_inc(v_keyName_349_);
v___x_350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_350_, 0, v_keyName_349_);
lean_ctor_set(v___x_350_, 1, v_module_343_);
v___x_351_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_352_ = 0;
v___x_353_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_val_346_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_task_pure(v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_342_);
lean_ctor_set(v___x_356_, 2, v___x_351_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*3, v___x_352_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_350_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_a_328_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v___x_345_);
v___x_359_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_360_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_361_ = lean_string_append(v___x_359_, v___x_360_);
lean_dec_ref(v___x_360_);
v___x_362_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_363_ = lean_string_append(v___x_361_, v___x_362_);
v___x_364_ = 1;
v___x_365_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_343_, v___x_364_);
v___x_366_ = lean_string_append(v___x_363_, v___x_365_);
lean_dec_ref(v___x_365_);
v___x_367_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_368_ = lean_string_append(v___x_366_, v___x_367_);
v___x_369_ = 3;
v___x_370_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*1, v___x_369_);
v___x_371_ = lean_array_get_size(v_a_328_);
v___x_372_ = lean_array_push(v_a_328_, v___x_370_);
v___x_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
case 1:
{
lean_object* v_package_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_a_323_);
v_package_374_ = lean_ctor_get(v_self_321_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_self_321_);
if (v_isSharedCheck_437_ == 0)
{
v___x_376_ = v_self_321_;
v_isShared_377_ = v_isSharedCheck_437_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_package_374_);
lean_dec(v_self_321_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_437_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v_a_379_; lean_object* v___x_394_; lean_object* v_a_396_; lean_object* v_a_397_; 
v___x_394_ = l_Lake_instDataKindPackage;
switch(lean_obj_tag(v_package_374_))
{
case 0:
{
lean_dec_ref(v_root_320_);
v_a_396_ = v_defaultPkg_319_;
v_a_397_ = v_a_328_;
goto v___jp_395_;
}
case 2:
{
lean_object* v_toContext_410_; lean_object* v_packageMap_411_; lean_object* v___x_412_; 
lean_dec_ref(v_defaultPkg_319_);
v_toContext_410_ = lean_ctor_get(v_a_327_, 1);
v_packageMap_411_ = lean_ctor_get(v_toContext_410_, 5);
v___x_412_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_411_, v_package_374_);
if (lean_obj_tag(v___x_412_) == 1)
{
lean_object* v_val_413_; 
lean_dec_ref_known(v_package_374_, 2);
lean_dec_ref(v_root_320_);
v_val_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v___x_412_, 1);
v_a_396_ = v_val_413_;
v_a_397_ = v_a_328_;
goto v___jp_395_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v___x_412_);
lean_del_object(v___x_376_);
v___x_414_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_415_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_416_ = lean_string_append(v___x_414_, v___x_415_);
lean_dec_ref(v___x_415_);
v___x_417_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_418_ = lean_string_append(v___x_416_, v___x_417_);
v___x_419_ = 1;
v___x_420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_374_, v___x_419_);
v___x_421_ = lean_string_append(v___x_418_, v___x_420_);
lean_dec_ref(v___x_420_);
v___x_422_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_423_ = lean_string_append(v___x_421_, v___x_422_);
v___x_424_ = 3;
v___x_425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*1, v___x_424_);
v___x_426_ = lean_array_get_size(v_a_328_);
v___x_427_ = lean_array_push(v_a_328_, v___x_425_);
v_a_339_ = v___x_426_;
v_a_340_ = v___x_427_;
goto v___jp_338_;
}
}
default: 
{
lean_object* v_toContext_428_; lean_object* v_packages_429_; lean_object* v___x_430_; size_t v_sz_431_; size_t v___x_432_; lean_object* v___x_433_; lean_object* v_fst_434_; 
lean_dec_ref(v_defaultPkg_319_);
v_toContext_428_ = lean_ctor_get(v_a_327_, 1);
v_packages_429_ = lean_ctor_get(v_toContext_428_, 4);
v___x_430_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_431_ = lean_array_size(v_packages_429_);
v___x_432_ = ((size_t)0ULL);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_374_, v_packages_429_, v_sz_431_, v___x_432_, v___x_430_);
v_fst_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_fst_434_);
lean_dec_ref(v___x_433_);
if (lean_obj_tag(v_fst_434_) == 0)
{
lean_del_object(v___x_376_);
v_a_379_ = v_a_328_;
goto v___jp_378_;
}
else
{
lean_object* v_val_435_; 
v_val_435_ = lean_ctor_get(v_fst_434_, 0);
lean_inc(v_val_435_);
lean_dec_ref_known(v_fst_434_, 1);
if (lean_obj_tag(v_val_435_) == 1)
{
lean_object* v_val_436_; 
lean_dec(v_package_374_);
lean_dec_ref(v_root_320_);
v_val_436_ = lean_ctor_get(v_val_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v_val_435_, 1);
v_a_396_ = v_val_436_;
v_a_397_ = v_a_328_;
goto v___jp_395_;
}
else
{
lean_dec(v_val_435_);
lean_del_object(v___x_376_);
v_a_379_ = v_a_328_;
goto v___jp_378_;
}
}
}
}
v___jp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_380_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_381_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
lean_dec_ref(v___x_381_);
v___x_383_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_384_ = lean_string_append(v___x_382_, v___x_383_);
v___x_385_ = 1;
v___x_386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_374_, v___x_385_);
v___x_387_ = lean_string_append(v___x_384_, v___x_386_);
lean_dec_ref(v___x_386_);
v___x_388_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_389_ = lean_string_append(v___x_387_, v___x_388_);
v___x_390_ = 3;
v___x_391_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*1, v___x_390_);
v___x_392_ = lean_array_get_size(v_a_379_);
v___x_393_ = lean_array_push(v_a_379_, v___x_391_);
v_a_339_ = v___x_392_;
v_a_340_ = v___x_393_;
goto v___jp_338_;
}
v___jp_395_:
{
lean_object* v_keyName_398_; lean_object* v___x_400_; 
v_keyName_398_ = lean_ctor_get(v_a_396_, 2);
lean_inc(v_keyName_398_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_keyName_398_);
v___x_400_ = v___x_376_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_keyName_398_);
v___x_400_ = v_reuseFailAlloc_409_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_401_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_402_ = 0;
v___x_403_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_a_396_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_task_pure(v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_394_);
lean_ctor_set(v___x_406_, 2, v___x_401_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*3, v___x_402_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_400_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_a_397_);
return v___x_408_;
}
}
}
}
case 2:
{
lean_object* v_package_438_; lean_object* v_module_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_a_323_);
v_package_438_ = lean_ctor_get(v_self_321_, 0);
v_module_439_ = lean_ctor_get(v_self_321_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_self_321_);
if (v_isSharedCheck_524_ == 0)
{
v___x_441_ = v_self_321_;
v_isShared_442_ = v_isSharedCheck_524_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_module_439_);
lean_inc(v_package_438_);
lean_dec(v_self_321_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_524_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v_a_444_; lean_object* v_a_445_; lean_object* v_a_482_; 
switch(lean_obj_tag(v_package_438_))
{
case 0:
{
v_a_444_ = v_defaultPkg_319_;
v_a_445_ = v_a_328_;
goto v___jp_443_;
}
case 2:
{
lean_object* v_toContext_497_; lean_object* v_packageMap_498_; lean_object* v___x_499_; 
lean_dec_ref(v_defaultPkg_319_);
v_toContext_497_ = lean_ctor_get(v_a_327_, 1);
v_packageMap_498_ = lean_ctor_get(v_toContext_497_, 5);
v___x_499_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_498_, v_package_438_);
if (lean_obj_tag(v___x_499_) == 1)
{
lean_object* v_val_500_; 
lean_dec_ref_known(v_package_438_, 2);
v_val_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_500_);
lean_dec_ref_known(v___x_499_, 1);
v_a_444_ = v_val_500_;
v_a_445_ = v_a_328_;
goto v___jp_443_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_499_);
lean_del_object(v___x_441_);
lean_dec(v_module_439_);
v___x_501_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_502_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
lean_dec_ref(v___x_502_);
v___x_504_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_505_ = lean_string_append(v___x_503_, v___x_504_);
v___x_506_ = 1;
v___x_507_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_438_, v___x_506_);
v___x_508_ = lean_string_append(v___x_505_, v___x_507_);
lean_dec_ref(v___x_507_);
v___x_509_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
v___x_511_ = 3;
v___x_512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1, v___x_511_);
v___x_513_ = lean_array_get_size(v_a_328_);
v___x_514_ = lean_array_push(v_a_328_, v___x_512_);
v_a_335_ = v___x_513_;
v_a_336_ = v___x_514_;
goto v___jp_334_;
}
}
default: 
{
lean_object* v_toContext_515_; lean_object* v_packages_516_; lean_object* v___x_517_; size_t v_sz_518_; size_t v___x_519_; lean_object* v___x_520_; lean_object* v_fst_521_; 
lean_dec_ref(v_defaultPkg_319_);
v_toContext_515_ = lean_ctor_get(v_a_327_, 1);
v_packages_516_ = lean_ctor_get(v_toContext_515_, 4);
v___x_517_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_518_ = lean_array_size(v_packages_516_);
v___x_519_ = ((size_t)0ULL);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_438_, v_packages_516_, v_sz_518_, v___x_519_, v___x_517_);
v_fst_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_fst_521_);
lean_dec_ref(v___x_520_);
if (lean_obj_tag(v_fst_521_) == 0)
{
lean_del_object(v___x_441_);
lean_dec(v_module_439_);
v_a_482_ = v_a_328_;
goto v___jp_481_;
}
else
{
lean_object* v_val_522_; 
v_val_522_ = lean_ctor_get(v_fst_521_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v_fst_521_, 1);
if (lean_obj_tag(v_val_522_) == 1)
{
lean_object* v_val_523_; 
lean_dec(v_package_438_);
v_val_523_ = lean_ctor_get(v_val_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v_val_522_, 1);
v_a_444_ = v_val_523_;
v_a_445_ = v_a_328_;
goto v___jp_443_;
}
else
{
lean_dec(v_val_522_);
lean_del_object(v___x_441_);
lean_dec(v_module_439_);
v_a_482_ = v_a_328_;
goto v___jp_481_;
}
}
}
}
v___jp_443_:
{
lean_object* v___x_446_; 
lean_inc_ref(v_a_444_);
lean_inc(v_module_439_);
v___x_446_ = l_Lake_Package_findTargetModule_x3f(v_module_439_, v_a_444_);
if (lean_obj_tag(v___x_446_) == 1)
{
lean_object* v_val_447_; lean_object* v_keyName_448_; lean_object* v___x_450_; 
lean_dec_ref(v_root_320_);
v_val_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v___x_446_, 1);
v_keyName_448_ = lean_ctor_get(v_a_444_, 2);
lean_inc(v_keyName_448_);
lean_dec_ref(v_a_444_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v_keyName_448_);
v___x_450_ = v___x_441_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_keyName_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_module_439_);
v___x_450_ = v_reuseFailAlloc_459_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_451_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_452_ = 0;
v___x_453_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_val_447_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_task_pure(v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_342_);
lean_ctor_set(v___x_456_, 2, v___x_451_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*3, v___x_452_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_450_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v_a_445_);
return v___x_458_;
}
}
else
{
lean_object* v_baseName_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v___x_446_);
lean_del_object(v___x_441_);
v_baseName_460_ = lean_ctor_get(v_a_444_, 1);
lean_inc(v_baseName_460_);
lean_dec_ref(v_a_444_);
v___x_461_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_462_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_463_ = lean_string_append(v___x_461_, v___x_462_);
lean_dec_ref(v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6));
v___x_465_ = lean_string_append(v___x_463_, v___x_464_);
v___x_466_ = 1;
v___x_467_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_439_, v___x_466_);
v___x_468_ = lean_string_append(v___x_465_, v___x_467_);
lean_dec_ref(v___x_467_);
v___x_469_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
v___x_470_ = lean_string_append(v___x_468_, v___x_469_);
v___x_471_ = 0;
v___x_472_ = l_Lean_Name_toString(v_baseName_460_, v___x_471_);
v___x_473_ = lean_string_append(v___x_470_, v___x_472_);
lean_dec_ref(v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
v___x_476_ = 3;
v___x_477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
v___x_478_ = lean_array_get_size(v_a_445_);
v___x_479_ = lean_array_push(v_a_445_, v___x_477_);
v___x_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
return v___x_480_;
}
}
v___jp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_483_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_484_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_485_ = lean_string_append(v___x_483_, v___x_484_);
lean_dec_ref(v___x_484_);
v___x_486_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_487_ = lean_string_append(v___x_485_, v___x_486_);
v___x_488_ = 1;
v___x_489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_438_, v___x_488_);
v___x_490_ = lean_string_append(v___x_487_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
v___x_493_ = 3;
v___x_494_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*1, v___x_493_);
v___x_495_ = lean_array_get_size(v_a_482_);
v___x_496_ = lean_array_push(v_a_482_, v___x_494_);
v_a_335_ = v___x_495_;
v_a_336_ = v___x_496_;
goto v___jp_334_;
}
}
}
case 3:
{
lean_object* v_package_525_; lean_object* v_target_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_676_; 
v_package_525_ = lean_ctor_get(v_self_321_, 0);
v_target_526_ = lean_ctor_get(v_self_321_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_self_321_);
if (v_isSharedCheck_676_ == 0)
{
v___x_528_ = v_self_321_;
v_isShared_529_ = v_isSharedCheck_676_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_target_526_);
lean_inc(v_package_525_);
lean_dec(v_self_321_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_676_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_a_531_; lean_object* v_a_532_; lean_object* v_a_634_; 
switch(lean_obj_tag(v_package_525_))
{
case 0:
{
v_a_531_ = v_defaultPkg_319_;
v_a_532_ = v_a_328_;
goto v___jp_530_;
}
case 2:
{
lean_object* v_toContext_649_; lean_object* v_packageMap_650_; lean_object* v___x_651_; 
lean_dec_ref(v_defaultPkg_319_);
v_toContext_649_ = lean_ctor_get(v_a_327_, 1);
v_packageMap_650_ = lean_ctor_get(v_toContext_649_, 5);
v___x_651_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_650_, v_package_525_);
if (lean_obj_tag(v___x_651_) == 1)
{
lean_object* v_val_652_; 
lean_dec_ref_known(v_package_525_, 2);
v_val_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v___x_651_, 1);
v_a_531_ = v_val_652_;
v_a_532_ = v_a_328_;
goto v___jp_530_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v___x_651_);
lean_del_object(v___x_528_);
lean_dec(v_target_526_);
lean_dec_ref(v_a_323_);
v___x_653_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_654_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_655_ = lean_string_append(v___x_653_, v___x_654_);
lean_dec_ref(v___x_654_);
v___x_656_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_657_ = lean_string_append(v___x_655_, v___x_656_);
v___x_658_ = 1;
v___x_659_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_525_, v___x_658_);
v___x_660_ = lean_string_append(v___x_657_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
v___x_663_ = 3;
v___x_664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set_uint8(v___x_664_, sizeof(void*)*1, v___x_663_);
v___x_665_ = lean_array_get_size(v_a_328_);
v___x_666_ = lean_array_push(v_a_328_, v___x_664_);
v_a_331_ = v___x_665_;
v_a_332_ = v___x_666_;
goto v___jp_330_;
}
}
default: 
{
lean_object* v_toContext_667_; lean_object* v_packages_668_; lean_object* v___x_669_; size_t v_sz_670_; size_t v___x_671_; lean_object* v___x_672_; lean_object* v_fst_673_; 
lean_dec_ref(v_defaultPkg_319_);
v_toContext_667_ = lean_ctor_get(v_a_327_, 1);
v_packages_668_ = lean_ctor_get(v_toContext_667_, 4);
v___x_669_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_670_ = lean_array_size(v_packages_668_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_525_, v_packages_668_, v_sz_670_, v___x_671_, v___x_669_);
v_fst_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_fst_673_);
lean_dec_ref(v___x_672_);
if (lean_obj_tag(v_fst_673_) == 0)
{
lean_del_object(v___x_528_);
lean_dec(v_target_526_);
lean_dec_ref(v_a_323_);
v_a_634_ = v_a_328_;
goto v___jp_633_;
}
else
{
lean_object* v_val_674_; 
v_val_674_ = lean_ctor_get(v_fst_673_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_fst_673_, 1);
if (lean_obj_tag(v_val_674_) == 1)
{
lean_object* v_val_675_; 
lean_dec(v_package_525_);
v_val_675_ = lean_ctor_get(v_val_674_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v_val_674_, 1);
v_a_531_ = v_val_675_;
v_a_532_ = v_a_328_;
goto v___jp_530_;
}
else
{
lean_dec(v_val_674_);
lean_del_object(v___x_528_);
lean_dec(v_target_526_);
lean_dec_ref(v_a_323_);
v_a_634_ = v_a_328_;
goto v___jp_633_;
}
}
}
}
v___jp_530_:
{
lean_object* v_baseName_533_; lean_object* v_keyName_534_; lean_object* v___x_536_; 
v_baseName_533_ = lean_ctor_get(v_a_531_, 1);
v_keyName_534_ = lean_ctor_get(v_a_531_, 2);
lean_inc(v_target_526_);
lean_inc(v_keyName_534_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v_keyName_534_);
v___x_536_ = v___x_528_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_keyName_534_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_target_526_);
v___x_536_ = v_reuseFailAlloc_632_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
if (v_facetless_322_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref(v_root_320_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_a_531_);
lean_ctor_set(v___x_537_, 1, v_target_526_);
lean_inc_ref(v_a_327_);
lean_inc(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
v___x_538_ = lean_apply_7(v_a_323_, v___x_537_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_532_, lean_box(0));
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_a_540_ = lean_ctor_get(v___x_538_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_542_ = v___x_538_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_536_);
lean_ctor_set(v___x_544_, 1, v_a_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_a_540_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v___x_536_);
v_a_549_ = lean_ctor_get(v___x_538_, 0);
v_a_550_ = lean_ctor_get(v___x_538_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_538_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_inc(v_a_549_);
lean_dec(v___x_538_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_549_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v___x_558_; 
v___x_558_ = l_Lake_Package_findTargetDecl_x3f(v_target_526_, v_a_531_);
if (lean_obj_tag(v___x_558_) == 1)
{
lean_object* v_val_559_; lean_object* v_name_560_; lean_object* v_kind_561_; lean_object* v_config_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_root_320_);
v_val_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v___x_558_, 1);
v_name_560_ = lean_ctor_get(v_val_559_, 1);
v_kind_561_ = lean_ctor_get(v_val_559_, 2);
v_config_562_ = lean_ctor_get(v_val_559_, 3);
v_isSharedCheck_615_ = !lean_is_exclusive(v_val_559_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_val_559_, 0);
lean_dec(v_unused_616_);
v___x_564_ = v_val_559_;
v_isShared_565_ = v_isSharedCheck_615_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_config_562_);
lean_inc(v_kind_561_);
lean_inc(v_name_560_);
lean_dec(v_val_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_615_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; 
v___x_566_ = l_Lean_Name_isAnonymous(v_kind_561_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
lean_dec(v_target_526_);
v___x_567_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9));
lean_inc(v_kind_561_);
v___x_568_ = l_Lean_Name_str___override(v_kind_561_, v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v_a_531_);
lean_ctor_set(v___x_569_, 1, v_name_560_);
lean_ctor_set(v___x_569_, 2, v_config_562_);
lean_inc(v___x_568_);
lean_inc_ref(v___x_536_);
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 1);
lean_ctor_set(v___x_564_, 3, v___x_568_);
lean_ctor_set(v___x_564_, 2, v___x_569_);
lean_ctor_set(v___x_564_, 1, v_kind_561_);
lean_ctor_set(v___x_564_, 0, v___x_536_);
v___x_571_ = v___x_564_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_kind_561_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v___x_568_);
v___x_571_ = v_reuseFailAlloc_593_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
lean_inc_ref(v_a_327_);
lean_inc(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
v___x_572_ = lean_apply_7(v_a_323_, v___x_571_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_532_, lean_box(0));
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_583_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_a_574_ = lean_ctor_get(v___x_572_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_583_ == 0)
{
v___x_576_ = v___x_572_;
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_583_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_536_);
lean_ctor_set(v___x_578_, 1, v___x_568_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_a_573_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_579_);
v___x_581_ = v___x_576_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_a_574_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v___x_568_);
lean_dec_ref(v___x_536_);
v_a_584_ = lean_ctor_get(v___x_572_, 0);
v_a_585_ = lean_ctor_get(v___x_572_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_572_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_inc(v_a_584_);
lean_dec(v___x_572_);
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
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_584_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_a_585_);
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
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_del_object(v___x_564_);
lean_dec(v_config_562_);
lean_dec(v_kind_561_);
lean_dec(v_name_560_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_a_531_);
lean_ctor_set(v___x_594_, 1, v_target_526_);
lean_inc_ref(v_a_327_);
lean_inc(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
v___x_595_ = lean_apply_7(v_a_323_, v___x_594_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_532_, lean_box(0));
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_605_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_a_597_ = lean_ctor_get(v___x_595_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_605_ == 0)
{
v___x_599_ = v___x_595_;
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_605_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_536_);
lean_ctor_set(v___x_601_, 1, v_a_596_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_601_);
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_597_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
else
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v___x_536_);
v_a_606_ = lean_ctor_get(v___x_595_, 0);
v_a_607_ = lean_ctor_get(v___x_595_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_595_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_inc(v_a_606_);
lean_dec(v___x_595_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_inc(v_baseName_533_);
lean_dec(v___x_558_);
lean_dec_ref(v___x_536_);
lean_dec_ref(v_a_531_);
lean_dec(v_target_526_);
lean_dec_ref(v_a_323_);
v___x_617_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_618_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_619_ = lean_string_append(v___x_617_, v___x_618_);
lean_dec_ref(v___x_618_);
v___x_620_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10));
v___x_621_ = lean_string_append(v___x_619_, v___x_620_);
v___x_622_ = 0;
v___x_623_ = l_Lean_Name_toString(v_baseName_533_, v___x_622_);
v___x_624_ = lean_string_append(v___x_621_, v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
v___x_627_ = 3;
v___x_628_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*1, v___x_627_);
v___x_629_ = lean_array_get_size(v_a_532_);
v___x_630_ = lean_array_push(v_a_532_, v___x_628_);
v___x_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
return v___x_631_;
}
}
}
}
v___jp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_635_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_636_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
v___x_640_ = 1;
v___x_641_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_525_, v___x_640_);
v___x_642_ = lean_string_append(v___x_639_, v___x_641_);
lean_dec_ref(v___x_641_);
v___x_643_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_644_ = lean_string_append(v___x_642_, v___x_643_);
v___x_645_ = 3;
v___x_646_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_645_);
v___x_647_ = lean_array_get_size(v_a_634_);
v___x_648_ = lean_array_push(v_a_634_, v___x_646_);
v_a_331_ = v___x_647_;
v_a_332_ = v___x_648_;
goto v___jp_330_;
}
}
}
default: 
{
lean_object* v_target_677_; lean_object* v_facet_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_749_; 
v_target_677_ = lean_ctor_get(v_self_321_, 0);
v_facet_678_ = lean_ctor_get(v_self_321_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_self_321_);
if (v_isSharedCheck_749_ == 0)
{
v___x_680_ = v_self_321_;
v_isShared_681_ = v_isSharedCheck_749_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_facet_678_);
lean_inc(v_target_677_);
lean_dec(v_self_321_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_749_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
uint8_t v___x_682_; lean_object* v___x_683_; 
v___x_682_ = 0;
lean_inc_ref(v_a_323_);
lean_inc_ref(v_target_677_);
lean_inc_ref(v_root_320_);
v___x_683_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_319_, v_root_320_, v_target_677_, v___x_682_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v_snd_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_747_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
v_snd_685_ = lean_ctor_get(v_a_684_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_a_684_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v_a_684_, 0);
lean_dec(v_unused_748_);
v___x_687_ = v_a_684_;
v_isShared_688_ = v_isSharedCheck_747_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_685_);
lean_dec(v_a_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_747_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_745_; 
v_a_689_ = lean_ctor_get(v___x_683_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v___x_683_, 0);
lean_dec(v_unused_746_);
v___x_691_ = v___x_683_;
v_isShared_692_ = v_isSharedCheck_745_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_683_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_745_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_kind_693_; lean_object* v___y_695_; uint8_t v___x_732_; 
v_kind_693_ = lean_ctor_get(v_snd_685_, 1);
v___x_732_ = l_Lean_Name_isAnonymous(v_kind_693_);
if (v___x_732_ == 0)
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_Name_isAnonymous(v_facet_678_);
if (v___x_733_ == 0)
{
v___y_695_ = v_facet_678_;
goto v___jp_694_;
}
else
{
lean_object* v___x_734_; 
lean_dec(v_facet_678_);
v___x_734_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12));
v___y_695_ = v___x_734_;
goto v___jp_694_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_del_object(v___x_691_);
lean_del_object(v___x_687_);
lean_dec(v_snd_685_);
lean_del_object(v___x_680_);
lean_dec(v_facet_678_);
lean_dec_ref(v_target_677_);
lean_dec_ref(v_a_323_);
v___x_735_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_736_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_737_ = lean_string_append(v___x_735_, v___x_736_);
lean_dec_ref(v___x_736_);
v___x_738_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
v___x_739_ = lean_string_append(v___x_737_, v___x_738_);
v___x_740_ = 3;
v___x_741_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*1, v___x_740_);
v___x_742_ = lean_array_get_size(v_a_689_);
v___x_743_ = lean_array_push(v_a_689_, v___x_741_);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
return v___x_744_;
}
v___jp_694_:
{
lean_object* v_toContext_696_; lean_object* v_facetConfigs_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_toContext_696_ = lean_ctor_get(v_a_327_, 1);
v_facetConfigs_697_ = lean_ctor_get(v_toContext_696_, 6);
lean_inc(v_kind_693_);
v___x_698_ = l_Lean_Name_append(v_kind_693_, v___y_695_);
v___x_699_ = l_Lake_FacetConfigMap_get_x3f(v___x_698_, v_facetConfigs_697_);
if (lean_obj_tag(v___x_699_) == 1)
{
lean_object* v_val_700_; lean_object* v_outKind_701_; lean_object* v___f_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec_ref(v_root_320_);
v_val_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___x_699_, 1);
v_outKind_701_ = lean_ctor_get(v_val_700_, 2);
lean_inc(v_outKind_701_);
lean_dec(v_val_700_);
lean_inc(v___x_698_);
lean_inc(v_kind_693_);
lean_inc_ref(v_target_677_);
v___f_702_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 11, 3);
lean_closure_set(v___f_702_, 0, v_target_677_);
lean_closure_set(v___f_702_, 1, v_kind_693_);
lean_closure_set(v___f_702_, 2, v___x_698_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_705_ = l_Lake_Job_bindM___redArg(v_outKind_701_, v_snd_685_, v___f_702_, v___x_703_, v___x_682_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v___x_704_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_698_);
v___x_707_ = v___x_680_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_target_677_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_698_);
v___x_707_ = v_reuseFailAlloc_714_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_705_);
lean_ctor_set(v___x_687_, 0, v___x_707_);
v___x_709_ = v___x_687_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_705_);
v___x_709_ = v_reuseFailAlloc_713_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_709_);
v___x_711_ = v___x_691_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_a_689_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
lean_dec(v___x_699_);
lean_del_object(v___x_687_);
lean_dec(v_snd_685_);
lean_del_object(v___x_680_);
lean_dec_ref(v_target_677_);
lean_dec_ref(v_a_323_);
v___x_715_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_716_ = l_Lake_PartialBuildKey_toString(v_root_320_);
v___x_717_ = lean_string_append(v___x_715_, v___x_716_);
lean_dec_ref(v___x_716_);
v___x_718_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
v___x_719_ = lean_string_append(v___x_717_, v___x_718_);
v___x_720_ = 1;
v___x_721_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_698_, v___x_720_);
v___x_722_ = lean_string_append(v___x_719_, v___x_721_);
lean_dec_ref(v___x_721_);
v___x_723_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_724_ = lean_string_append(v___x_722_, v___x_723_);
v___x_725_ = 3;
v___x_726_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*1, v___x_725_);
v___x_727_ = lean_array_get_size(v_a_689_);
v___x_728_ = lean_array_push(v_a_689_, v___x_726_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 1);
lean_ctor_set(v___x_691_, 1, v___x_728_);
lean_ctor_set(v___x_691_, 0, v___x_727_);
v___x_730_ = v___x_691_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_680_);
lean_dec(v_facet_678_);
lean_dec_ref(v_target_677_);
lean_dec_ref(v_a_323_);
lean_dec_ref(v_root_320_);
return v___x_683_;
}
}
}
}
v___jp_330_:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v_a_331_);
lean_ctor_set(v___x_333_, 1, v_a_332_);
return v___x_333_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object* v_defaultPkg_750_, lean_object* v_root_751_, lean_object* v_self_752_, lean_object* v_facetless_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
uint8_t v_facetless_boxed_761_; lean_object* v_res_762_; 
v_facetless_boxed_761_ = lean_unbox(v_facetless_753_);
v_res_762_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_750_, v_root_751_, v_self_752_, v_facetless_boxed_761_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec(v_a_756_);
lean_dec(v_a_755_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(lean_object* v_00_u03b2_763_, lean_object* v_inst_764_, lean_object* v_t_765_, lean_object* v_k_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_765_, v_k_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(lean_object* v_00_u03b2_768_, lean_object* v_inst_769_, lean_object* v_t_770_, lean_object* v_k_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(v_00_u03b2_768_, v_inst_769_, v_t_770_, v_k_771_);
lean_dec(v_k_771_);
lean_dec(v_t_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object* v_defaultPkg_773_, lean_object* v_self_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_782_ = 1;
lean_inc_ref(v_self_774_);
v___x_783_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_773_, v_self_774_, v_self_774_, v___x_782_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore___boxed(lean_object* v_defaultPkg_784_, lean_object* v_self_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lake_PartialBuildKey_fetchInCore(v_defaultPkg_784_, v_self_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec(v_a_788_);
lean_dec(v_a_787_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object* v_defaultPkg_794_, lean_object* v_self_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
uint8_t v___x_803_; lean_object* v___x_804_; 
v___x_803_ = 1;
lean_inc_ref(v_self_795_);
v___x_804_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_794_, v_self_795_, v_self_795_, v___x_803_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_815_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_a_806_ = lean_ctor_get(v___x_804_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_815_ == 0)
{
v___x_808_ = v___x_804_;
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_snd_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v_snd_810_ = lean_ctor_get(v_a_805_, 1);
lean_inc(v_snd_810_);
lean_dec(v_a_805_);
v___x_811_ = l_Lake_Job_toOpaque___redArg(v_snd_810_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_806_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v_a_816_; lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
v_a_816_ = lean_ctor_get(v___x_804_, 0);
v_a_817_ = lean_ctor_get(v___x_804_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_804_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_inc(v_a_816_);
lean_dec(v___x_804_);
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
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn___boxed(lean_object* v_defaultPkg_825_, lean_object* v_self_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lake_PartialBuildKey_fetchIn(v_defaultPkg_825_, v_self_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec(v_a_829_);
lean_dec(v_a_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(lean_object* v_target_835_, lean_object* v_kind_836_, lean_object* v_facet_837_, lean_object* v_data_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_log_846_; uint8_t v_action_847_; uint8_t v_wantsRebuild_848_; uint8_t v_canceled_849_; lean_object* v_trace_850_; lean_object* v_buildTime_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_881_; 
v_log_846_ = lean_ctor_get(v___y_844_, 0);
v_action_847_ = lean_ctor_get_uint8(v___y_844_, sizeof(void*)*3);
v_wantsRebuild_848_ = lean_ctor_get_uint8(v___y_844_, sizeof(void*)*3 + 1);
v_canceled_849_ = lean_ctor_get_uint8(v___y_844_, sizeof(void*)*3 + 2);
v_trace_850_ = lean_ctor_get(v___y_844_, 1);
v_buildTime_851_ = lean_ctor_get(v___y_844_, 2);
v_isSharedCheck_881_ = !lean_is_exclusive(v___y_844_);
if (v_isSharedCheck_881_ == 0)
{
v___x_853_ = v___y_844_;
v_isShared_854_ = v_isSharedCheck_881_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_buildTime_851_);
lean_inc(v_trace_850_);
lean_inc(v_log_846_);
lean_dec(v___y_844_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_881_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_855_, 0, v_target_835_);
lean_ctor_set(v___x_855_, 1, v_kind_836_);
lean_ctor_set(v___x_855_, 2, v_data_838_);
lean_ctor_set(v___x_855_, 3, v_facet_837_);
lean_inc_ref(v___y_843_);
lean_inc(v___y_842_);
lean_inc(v___y_841_);
lean_inc(v___y_840_);
v___x_856_ = lean_apply_7(v___y_839_, v___x_855_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v_log_846_, lean_box(0));
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_868_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_a_858_ = lean_ctor_get(v___x_856_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_868_ == 0)
{
v___x_860_ = v___x_856_;
v_isShared_861_ = v_isSharedCheck_868_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_868_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_a_858_);
v___x_863_ = v___x_853_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_858_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_trace_850_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_buildTime_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*3, v_action_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*3 + 1, v_wantsRebuild_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*3 + 2, v_canceled_849_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_863_);
v___x_865_ = v___x_860_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_857_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_880_; 
v_a_869_ = lean_ctor_get(v___x_856_, 0);
v_a_870_ = lean_ctor_get(v___x_856_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_880_ == 0)
{
v___x_872_ = v___x_856_;
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_inc(v_a_869_);
lean_dec(v___x_856_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_a_870_);
v___x_875_ = v___x_853_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_870_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_trace_850_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_buildTime_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3, v_action_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3 + 1, v_wantsRebuild_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*3 + 2, v_canceled_849_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_869_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed(lean_object* v_target_882_, lean_object* v_kind_883_, lean_object* v_facet_884_, lean_object* v_data_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(v_target_882_, v_kind_883_, v_facet_884_, v_data_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec(v___y_888_);
lean_dec(v___y_887_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(lean_object* v_root_894_, lean_object* v_self_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lake_instDataKindModule;
switch(lean_obj_tag(v_self_895_))
{
case 0:
{
lean_object* v_module_904_; lean_object* v_toContext_905_; lean_object* v___x_906_; 
lean_dec_ref(v_a_896_);
v_module_904_ = lean_ctor_get(v_self_895_, 0);
lean_inc_n(v_module_904_, 2);
lean_dec_ref_known(v_self_895_, 1);
v_toContext_905_ = lean_ctor_get(v_a_900_, 1);
v___x_906_ = l_Lake_Workspace_findModule_x3f(v_module_904_, v_toContext_905_);
if (lean_obj_tag(v___x_906_) == 1)
{
lean_object* v_val_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_module_904_);
lean_dec_ref(v_root_894_);
v_val_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_val_907_);
lean_dec_ref_known(v___x_906_, 1);
v___x_908_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_909_ = 0;
v___x_910_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_val_907_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_task_pure(v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_903_);
lean_ctor_set(v___x_913_, 2, v___x_908_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*3, v___x_909_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v_a_901_);
return v___x_914_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v___x_906_);
v___x_915_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_916_ = l_Lake_BuildKey_toString(v_root_894_);
v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
lean_dec_ref(v___x_916_);
v___x_918_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
v___x_920_ = 1;
v___x_921_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_904_, v___x_920_);
v___x_922_ = lean_string_append(v___x_919_, v___x_921_);
lean_dec_ref(v___x_921_);
v___x_923_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
v___x_925_ = 3;
v___x_926_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*1, v___x_925_);
v___x_927_ = lean_array_get_size(v_a_901_);
v___x_928_ = lean_array_push(v_a_901_, v___x_926_);
v___x_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
return v___x_929_;
}
}
case 1:
{
lean_object* v_toContext_930_; lean_object* v_package_931_; lean_object* v_packageMap_932_; lean_object* v___x_933_; 
lean_dec_ref(v_a_896_);
v_toContext_930_ = lean_ctor_get(v_a_900_, 1);
v_package_931_ = lean_ctor_get(v_self_895_, 0);
lean_inc(v_package_931_);
lean_dec_ref_known(v_self_895_, 1);
v_packageMap_932_ = lean_ctor_get(v_toContext_930_, 5);
v___x_933_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_932_, v_package_931_);
if (lean_obj_tag(v___x_933_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_package_931_);
lean_dec_ref(v_root_894_);
v_val_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = l_Lake_instDataKindPackage;
v___x_936_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_937_ = 0;
v___x_938_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_val_934_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_task_pure(v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_935_);
lean_ctor_set(v___x_941_, 2, v___x_936_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*3, v___x_937_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_a_901_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v___x_933_);
v___x_943_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_944_ = l_Lake_BuildKey_toString(v_root_894_);
v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
lean_dec_ref(v___x_944_);
v___x_946_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
v___x_948_ = 1;
v___x_949_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_931_, v___x_948_);
v___x_950_ = lean_string_append(v___x_947_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
v___x_953_ = 3;
v___x_954_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*1, v___x_953_);
v___x_955_ = lean_array_get_size(v_a_901_);
v___x_956_ = lean_array_push(v_a_901_, v___x_954_);
v___x_957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
return v___x_957_;
}
}
case 2:
{
lean_object* v_toContext_958_; lean_object* v_package_959_; lean_object* v_module_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_a_896_);
v_toContext_958_ = lean_ctor_get(v_a_900_, 1);
v_package_959_ = lean_ctor_get(v_self_895_, 0);
v_module_960_ = lean_ctor_get(v_self_895_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_self_895_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_962_ = v_self_895_;
v_isShared_963_ = v_isSharedCheck_1018_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_module_960_);
lean_inc(v_package_959_);
lean_dec(v_self_895_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1018_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_packageMap_964_; lean_object* v___x_965_; 
v_packageMap_964_ = lean_ctor_get(v_toContext_958_, 5);
v___x_965_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_964_, v_package_959_);
if (lean_obj_tag(v___x_965_) == 1)
{
lean_object* v_val_966_; lean_object* v___x_967_; 
lean_dec(v_package_959_);
v_val_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_n(v_val_966_, 2);
lean_dec_ref_known(v___x_965_, 1);
lean_inc(v_module_960_);
v___x_967_ = l_Lake_Package_findTargetModule_x3f(v_module_960_, v_val_966_);
if (lean_obj_tag(v___x_967_) == 1)
{
lean_object* v_val_968_; lean_object* v___x_969_; uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
lean_dec(v_val_966_);
lean_dec(v_module_960_);
lean_dec_ref(v_root_894_);
v_val_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_val_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_970_ = 0;
v___x_971_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 0);
lean_ctor_set(v___x_962_, 1, v___x_971_);
lean_ctor_set(v___x_962_, 0, v_val_968_);
v___x_973_ = v___x_962_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_val_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_task_pure(v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_903_);
lean_ctor_set(v___x_975_, 2, v___x_969_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*3, v___x_970_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v_a_901_);
return v___x_976_;
}
}
else
{
lean_object* v_baseName_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec(v___x_967_);
v_baseName_978_ = lean_ctor_get(v_val_966_, 1);
lean_inc(v_baseName_978_);
lean_dec(v_val_966_);
v___x_979_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_980_ = l_Lake_BuildKey_toString(v_root_894_);
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = 1;
v___x_985_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_960_, v___x_984_);
v___x_986_ = lean_string_append(v___x_983_, v___x_985_);
lean_dec_ref(v___x_985_);
v___x_987_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
v___x_989_ = 0;
v___x_990_ = l_Lean_Name_toString(v_baseName_978_, v___x_989_);
v___x_991_ = lean_string_append(v___x_988_, v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_993_ = lean_string_append(v___x_991_, v___x_992_);
v___x_994_ = 3;
v___x_995_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_994_);
v___x_996_ = lean_array_get_size(v_a_901_);
v___x_997_ = lean_array_push(v_a_901_, v___x_995_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
lean_ctor_set(v___x_962_, 1, v___x_997_);
lean_ctor_set(v___x_962_, 0, v___x_996_);
v___x_999_ = v___x_962_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec(v___x_965_);
lean_dec(v_module_960_);
v___x_1001_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1002_ = l_Lake_BuildKey_toString(v_root_894_);
v___x_1003_ = lean_string_append(v___x_1001_, v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
v___x_1006_ = 1;
v___x_1007_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_959_, v___x_1006_);
v___x_1008_ = lean_string_append(v___x_1005_, v___x_1007_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_1010_ = lean_string_append(v___x_1008_, v___x_1009_);
v___x_1011_ = 3;
v___x_1012_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_1011_);
v___x_1013_ = lean_array_get_size(v_a_901_);
v___x_1014_ = lean_array_push(v_a_901_, v___x_1012_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
lean_ctor_set(v___x_962_, 1, v___x_1014_);
lean_ctor_set(v___x_962_, 0, v___x_1013_);
v___x_1016_ = v___x_962_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
case 3:
{
lean_object* v_toContext_1019_; lean_object* v_package_1020_; lean_object* v_target_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1049_; 
v_toContext_1019_ = lean_ctor_get(v_a_900_, 1);
v_package_1020_ = lean_ctor_get(v_self_895_, 0);
v_target_1021_ = lean_ctor_get(v_self_895_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_self_895_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1023_ = v_self_895_;
v_isShared_1024_ = v_isSharedCheck_1049_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_target_1021_);
lean_inc(v_package_1020_);
lean_dec(v_self_895_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1049_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_packageMap_1025_; lean_object* v___x_1026_; 
v_packageMap_1025_ = lean_ctor_get(v_toContext_1019_, 5);
v___x_1026_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_1025_, v_package_1020_);
if (lean_obj_tag(v___x_1026_) == 1)
{
lean_object* v_val_1027_; lean_object* v___x_1029_; 
lean_dec(v_package_1020_);
lean_dec_ref(v_root_894_);
v_val_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v___x_1026_, 1);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 0);
lean_ctor_set(v___x_1023_, 0, v_val_1027_);
v___x_1029_ = v___x_1023_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_val_1027_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_target_1021_);
v___x_1029_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc(v_a_898_);
lean_inc(v_a_897_);
v___x_1030_ = lean_apply_7(v_a_896_, v___x_1029_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, lean_box(0));
return v___x_1030_;
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
lean_dec(v___x_1026_);
lean_dec(v_target_1021_);
lean_dec_ref(v_a_896_);
v___x_1032_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1033_ = l_Lake_BuildKey_toString(v_root_894_);
v___x_1034_ = lean_string_append(v___x_1032_, v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1035_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
v___x_1037_ = 1;
v___x_1038_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_1020_, v___x_1037_);
v___x_1039_ = lean_string_append(v___x_1036_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
v___x_1042_ = 3;
v___x_1043_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*1, v___x_1042_);
v___x_1044_ = lean_array_get_size(v_a_901_);
v___x_1045_ = lean_array_push(v_a_901_, v___x_1043_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 1, v___x_1045_);
lean_ctor_set(v___x_1023_, 0, v___x_1044_);
v___x_1047_ = v___x_1023_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
default: 
{
lean_object* v_target_1050_; lean_object* v_facet_1051_; lean_object* v___x_1052_; 
v_target_1050_ = lean_ctor_get(v_self_895_, 0);
v_facet_1051_ = lean_ctor_get(v_self_895_, 1);
lean_inc_ref(v_a_896_);
lean_inc_ref(v_target_1050_);
lean_inc_ref(v_root_894_);
v___x_1052_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_root_894_, v_target_1050_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1101_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_a_1054_ = lean_ctor_get(v___x_1052_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1056_ = v___x_1052_;
v_isShared_1057_ = v_isSharedCheck_1101_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1101_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_kind_1058_; uint8_t v___x_1059_; 
v_kind_1058_ = lean_ctor_get(v_a_1053_, 1);
v___x_1059_ = l_Lean_Name_isAnonymous(v_kind_1058_);
if (v___x_1059_ == 0)
{
lean_object* v_toContext_1060_; lean_object* v_facetConfigs_1061_; lean_object* v___x_1062_; 
lean_inc(v_facet_1051_);
lean_inc_ref(v_target_1050_);
lean_dec_ref_known(v_self_895_, 2);
v_toContext_1060_ = lean_ctor_get(v_a_900_, 1);
v_facetConfigs_1061_ = lean_ctor_get(v_toContext_1060_, 6);
v___x_1062_ = l_Lake_FacetConfigMap_get_x3f(v_facet_1051_, v_facetConfigs_1061_);
if (lean_obj_tag(v___x_1062_) == 1)
{
lean_object* v_val_1063_; lean_object* v_outKind_1064_; lean_object* v___f_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_dec_ref(v_root_894_);
v_val_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v_outKind_1064_ = lean_ctor_get(v_val_1063_, 2);
lean_inc(v_outKind_1064_);
lean_dec(v_val_1063_);
lean_inc(v_kind_1058_);
v___f_1065_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed), 11, 3);
lean_closure_set(v___f_1065_, 0, v_target_1050_);
lean_closure_set(v___f_1065_, 1, v_kind_1058_);
lean_closure_set(v___f_1065_, 2, v_facet_1051_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_1068_ = l_Lake_Job_bindM___redArg(v_outKind_1064_, v_a_1053_, v___f_1065_, v___x_1066_, v___x_1059_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v___x_1067_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1068_);
v___x_1070_ = v___x_1056_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_a_1054_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_dec(v___x_1062_);
lean_dec(v_a_1053_);
lean_dec_ref(v_target_1050_);
lean_dec_ref(v_a_896_);
v___x_1072_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1073_ = l_Lake_BuildKey_toString(v_root_894_);
v___x_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
v___x_1076_ = lean_string_append(v___x_1074_, v___x_1075_);
v___x_1077_ = 1;
v___x_1078_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_1051_, v___x_1077_);
v___x_1079_ = lean_string_append(v___x_1076_, v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
v___x_1082_ = 3;
v___x_1083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
v___x_1084_ = lean_array_get_size(v_a_1054_);
v___x_1085_ = lean_array_push(v_a_1054_, v___x_1083_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 1);
lean_ctor_set(v___x_1056_, 1, v___x_1085_);
lean_ctor_set(v___x_1056_, 0, v___x_1084_);
v___x_1087_ = v___x_1056_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_dec(v_a_1053_);
lean_dec_ref(v_a_896_);
lean_dec_ref(v_root_894_);
v___x_1089_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1090_ = l_Lake_BuildKey_toString(v_self_895_);
v___x_1091_ = lean_string_append(v___x_1089_, v___x_1090_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
v___x_1094_ = 3;
v___x_1095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1094_);
v___x_1096_ = lean_array_get_size(v_a_1054_);
v___x_1097_ = lean_array_push(v_a_1054_, v___x_1095_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 1);
lean_ctor_set(v___x_1056_, 1, v___x_1097_);
lean_ctor_set(v___x_1056_, 0, v___x_1096_);
v___x_1099_ = v___x_1056_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_dec_ref_known(v_self_895_, 2);
lean_dec_ref(v_a_896_);
lean_dec_ref(v_root_894_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___boxed(lean_object* v_root_1102_, lean_object* v_self_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_root_1102_, v_self_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec(v_a_1105_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg(lean_object* v_self_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; 
lean_inc_ref(v_self_1112_);
v___x_1120_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_self_1112_, v_self_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg___boxed(lean_object* v_self_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lake_BuildKey_fetch___redArg(v_self_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec(v_a_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object* v_00_u03b1_1130_, lean_object* v_self_1131_, lean_object* v_inst_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
lean_inc_ref(v_self_1131_);
v___x_1140_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_self_1131_, v_self_1131_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_self_1142_, lean_object* v_inst_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lake_BuildKey_fetch(v_00_u03b1_1141_, v_self_1142_, v_inst_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec(v_a_1145_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg(lean_object* v_inst_1156_, lean_object* v_defaultPkg_1157_, lean_object* v_self_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
uint8_t v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = 1;
lean_inc_ref_n(v_self_1158_, 2);
v___x_1167_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1157_, v_self_1158_, v_self_1158_, v___x_1166_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1209_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_a_1169_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1171_ = v___x_1167_;
v_isShared_1172_ = v_isSharedCheck_1209_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1209_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___y_1174_; lean_object* v_snd_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1207_; 
v_snd_1192_ = lean_ctor_get(v_a_1168_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1168_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_a_1168_, 0);
lean_dec(v_unused_1208_);
v___x_1194_ = v_a_1168_;
v_isShared_1195_ = v_isSharedCheck_1207_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snd_1192_);
lean_dec(v_a_1168_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1207_;
goto v_resetjp_1193_;
}
v___jp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1175_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__0));
v___x_1176_ = l_Lake_PartialBuildKey_toString(v_self_1158_);
v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__1));
v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
v___x_1180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1156_, v___x_1166_);
v___x_1181_ = lean_string_append(v___x_1179_, v___x_1180_);
lean_dec_ref(v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__2));
v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_string_append(v___x_1183_, v___y_1174_);
lean_dec_ref(v___y_1174_);
v___x_1185_ = 3;
v___x_1186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*1, v___x_1185_);
v___x_1187_ = lean_array_get_size(v_a_1169_);
v___x_1188_ = lean_array_push(v_a_1169_, v___x_1186_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 1);
lean_ctor_set(v___x_1171_, 1, v___x_1188_);
lean_ctor_set(v___x_1171_, 0, v___x_1187_);
v___x_1190_ = v___x_1171_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
v_resetjp_1193_:
{
lean_object* v_kind_1196_; uint8_t v___x_1197_; 
v_kind_1196_ = lean_ctor_get(v_snd_1192_, 1);
v___x_1197_ = lean_name_eq(v_kind_1196_, v_inst_1156_);
if (v___x_1197_ == 0)
{
uint8_t v___x_1198_; 
lean_inc(v_kind_1196_);
lean_del_object(v___x_1194_);
lean_dec(v_snd_1192_);
v___x_1198_ = l_Lean_Name_isAnonymous(v_kind_1196_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1199_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_1200_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1196_, v___x_1166_);
v___x_1201_ = lean_string_append(v___x_1199_, v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = lean_string_append(v___x_1201_, v___x_1199_);
v___y_1174_ = v___x_1202_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1203_; 
lean_dec(v_kind_1196_);
v___x_1203_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__3));
v___y_1174_ = v___x_1203_;
goto v___jp_1173_;
}
}
else
{
lean_object* v___x_1205_; 
lean_del_object(v___x_1171_);
lean_dec_ref(v_self_1158_);
lean_dec(v_inst_1156_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v_a_1169_);
lean_ctor_set(v___x_1194_, 0, v_snd_1192_);
v___x_1205_ = v___x_1194_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_snd_1192_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_a_1169_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_self_1158_);
lean_dec(v_inst_1156_);
v_a_1210_ = lean_ctor_get(v___x_1167_, 0);
v_a_1211_ = lean_ctor_get(v___x_1167_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1167_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_inc(v_a_1210_);
lean_dec(v___x_1167_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1210_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg___boxed(lean_object* v_inst_1219_, lean_object* v_defaultPkg_1220_, lean_object* v_self_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lake_Target_fetchIn___redArg(v_inst_1219_, v_defaultPkg_1220_, v_self_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec(v_a_1223_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn(lean_object* v_00_u03b1_1230_, lean_object* v_inst_1231_, lean_object* v_defaultPkg_1232_, lean_object* v_self_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lake_Target_fetchIn___redArg(v_inst_1231_, v_defaultPkg_1232_, v_self_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_inst_1243_, lean_object* v_defaultPkg_1244_, lean_object* v_self_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lake_Target_fetchIn(v_00_u03b1_1242_, v_inst_1243_, v_defaultPkg_1244_, v_self_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec(v_a_1247_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0(lean_object* v_inst_1254_, lean_object* v_defaultPkg_1255_, lean_object* v_x_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lake_Target_fetchIn___redArg(v_inst_1254_, v_defaultPkg_1255_, v_x_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed(lean_object* v_inst_1265_, lean_object* v_defaultPkg_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lake_TargetArray_fetchIn___redArg___lam__0(v_inst_1265_, v_defaultPkg_1266_, v_x_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object* v_inst_1276_, lean_object* v_defaultPkg_1277_, lean_object* v_self_1278_, lean_object* v_traceCaption_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v_toApplicative_1288_; lean_object* v_toBind_1289_; lean_object* v_toFunctor_1290_; lean_object* v_toPure_1291_; lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; size_t v_sz_1306_; size_t v___x_1307_; lean_object* v___x_521__overap_1308_; lean_object* v___x_1309_; 
v___x_1287_ = l_instMonadBaseIO;
v_toApplicative_1288_ = lean_ctor_get(v___x_1287_, 0);
v_toBind_1289_ = lean_ctor_get(v___x_1287_, 1);
v_toFunctor_1290_ = lean_ctor_get(v_toApplicative_1288_, 0);
v_toPure_1291_ = lean_ctor_get(v_toApplicative_1288_, 1);
v___f_1292_ = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1292_, 0, v_inst_1276_);
lean_closure_set(v___f_1292_, 1, v_defaultPkg_1277_);
lean_inc_n(v_toBind_1289_, 3);
lean_inc_n(v_toPure_1291_, 5);
v___f_1293_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1293_, 0, v_toPure_1291_);
lean_closure_set(v___f_1293_, 1, v_toBind_1289_);
v___f_1294_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1294_, 0, v_toPure_1291_);
lean_closure_set(v___f_1294_, 1, v_toBind_1289_);
lean_inc_ref(v___f_1293_);
v___f_1295_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1295_, 0, v_toPure_1291_);
lean_closure_set(v___f_1295_, 1, v___f_1293_);
lean_inc_ref_n(v_toFunctor_1290_, 2);
v___f_1296_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1296_, 0, v_toFunctor_1290_);
lean_closure_set(v___f_1296_, 1, v_toPure_1291_);
lean_closure_set(v___f_1296_, 2, v_toBind_1289_);
v___x_1297_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1290_);
v___f_1298_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1298_, 0, v_toPure_1291_);
v___x_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v___f_1298_);
lean_ctor_set(v___x_1299_, 2, v___f_1296_);
lean_ctor_set(v___x_1299_, 3, v___f_1295_);
lean_ctor_set(v___x_1299_, 4, v___f_1294_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___f_1293_);
v___x_1301_ = l_ReaderT_instMonad___redArg(v___x_1300_);
v___x_1302_ = l_StateRefT_x27_instMonad___redArg(v___x_1301_);
v___x_1303_ = l_ReaderT_instMonad___redArg(v___x_1302_);
v___x_1304_ = l_ReaderT_instMonad___redArg(v___x_1303_);
v___x_1305_ = l_Lake_EquipT_instMonad___redArg(v___x_1304_);
v_sz_1306_ = lean_array_size(v_self_1278_);
v___x_1307_ = ((size_t)0ULL);
v___x_521__overap_1308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1305_, v___f_1292_, v_sz_1306_, v___x_1307_, v_self_1278_);
lean_inc_ref(v_a_1284_);
lean_inc(v_a_1283_);
lean_inc(v_a_1282_);
lean_inc(v_a_1281_);
v___x_1309_ = lean_apply_7(v___x_521__overap_1308_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, lean_box(0));
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_a_1311_ = lean_ctor_get(v___x_1309_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1313_ = v___x_1309_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = l_Lake_Job_collectArray___redArg(v_a_1310_, v_traceCaption_1279_);
lean_dec(v_a_1310_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_a_1311_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_traceCaption_1279_);
v_a_1320_ = lean_ctor_get(v___x_1309_, 0);
v_a_1321_ = lean_ctor_get(v___x_1309_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1309_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_inc(v_a_1320_);
lean_dec(v___x_1309_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1320_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___boxed(lean_object* v_inst_1329_, lean_object* v_defaultPkg_1330_, lean_object* v_self_1331_, lean_object* v_traceCaption_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lake_TargetArray_fetchIn___redArg(v_inst_1329_, v_defaultPkg_1330_, v_self_1331_, v_traceCaption_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec(v_a_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn(lean_object* v_00_u03b1_1341_, lean_object* v_inst_1342_, lean_object* v_defaultPkg_1343_, lean_object* v_self_1344_, lean_object* v_traceCaption_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lake_TargetArray_fetchIn___redArg(v_inst_1342_, v_defaultPkg_1343_, v_self_1344_, v_traceCaption_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_inst_1355_, lean_object* v_defaultPkg_1356_, lean_object* v_self_1357_, lean_object* v_traceCaption_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lake_TargetArray_fetchIn(v_00_u03b1_1354_, v_inst_1355_, v_defaultPkg_1356_, v_self_1357_, v_traceCaption_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec(v_a_1360_);
return v_res_1366_;
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
