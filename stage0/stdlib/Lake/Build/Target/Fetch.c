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
lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
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
static lean_once_cell_t l_Lake_TargetArray_fetchIn___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_TargetArray_fetchIn___redArg___closed__0;
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
lean_dec_ref(v_a_50_);
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
lean_inc(v_toContext_71_);
lean_dec_ref(v_a_50_);
v_packageMap_72_ = lean_ctor_get(v_toContext_71_, 6);
lean_inc(v_packageMap_72_);
lean_dec(v_toContext_71_);
v___x_73_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(v_name_49_);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_73_, v_packageMap_72_, v_name_49_);
if (lean_obj_tag(v___x_74_) == 1)
{
lean_object* v_val_75_; lean_object* v___x_76_; 
lean_dec_ref(v_name_49_);
lean_dec_ref(v_root_48_);
v_val_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v___x_74_);
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
lean_inc(v_toContext_92_);
lean_dec_ref(v_a_50_);
v_packages_93_ = lean_ctor_get(v_toContext_92_, 5);
lean_inc_ref(v_packages_93_);
lean_dec(v_toContext_92_);
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
lean_dec_ref(v_fst_101_);
if (lean_obj_tag(v_val_105_) == 1)
{
lean_object* v_val_106_; lean_object* v___x_108_; 
lean_dec(v_name_49_);
lean_dec_ref(v_root_48_);
v_val_106_ = lean_ctor_get(v_val_105_, 0);
lean_inc(v_val_106_);
lean_dec_ref(v_val_105_);
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
lean_dec_ref(v_a_126_);
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
lean_inc(v_toContext_147_);
lean_dec_ref(v_a_126_);
v_packageMap_148_ = lean_ctor_get(v_toContext_147_, 6);
lean_inc(v_packageMap_148_);
lean_dec(v_toContext_147_);
v___x_149_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(v_name_121_);
v___x_150_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_149_, v_packageMap_148_, v_name_121_);
if (lean_obj_tag(v___x_150_) == 1)
{
lean_object* v_val_151_; lean_object* v___x_152_; 
lean_dec_ref(v_name_121_);
lean_dec_ref(v_root_120_);
v_val_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v___x_150_);
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
lean_inc(v_toContext_168_);
lean_dec_ref(v_a_126_);
v_packages_169_ = lean_ctor_get(v_toContext_168_, 5);
lean_inc_ref(v_packages_169_);
lean_dec(v_toContext_168_);
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
lean_dec_ref(v_fst_177_);
if (lean_obj_tag(v_val_181_) == 1)
{
lean_object* v_val_182_; lean_object* v___x_184_; 
lean_dec(v_name_121_);
lean_dec_ref(v_root_120_);
v_val_182_ = lean_ctor_get(v_val_181_, 0);
lean_inc(v_val_182_);
lean_dec_ref(v_val_181_);
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
lean_object* v_log_210_; uint8_t v_action_211_; uint8_t v_wantsRebuild_212_; lean_object* v_trace_213_; lean_object* v_buildTime_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_244_; 
v_log_210_ = lean_ctor_get(v___y_208_, 0);
v_action_211_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*3);
v_wantsRebuild_212_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*3 + 1);
v_trace_213_ = lean_ctor_get(v___y_208_, 1);
v_buildTime_214_ = lean_ctor_get(v___y_208_, 2);
v_isSharedCheck_244_ = !lean_is_exclusive(v___y_208_);
if (v_isSharedCheck_244_ == 0)
{
v___x_216_ = v___y_208_;
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_buildTime_214_);
lean_inc(v_trace_213_);
lean_inc(v_log_210_);
lean_dec(v___y_208_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_218_, 0, v_target_199_);
lean_ctor_set(v___x_218_, 1, v_kind_200_);
lean_ctor_set(v___x_218_, 2, v_data_202_);
lean_ctor_set(v___x_218_, 3, v___x_201_);
v___x_219_ = lean_apply_7(v___y_203_, v___x_218_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v_log_210_, lean_box(0));
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_231_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_a_221_ = lean_ctor_get(v___x_219_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_231_ == 0)
{
v___x_223_ = v___x_219_;
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v_a_221_);
v___x_226_ = v___x_216_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_221_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_trace_213_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_buildTime_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*3, v_action_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*3 + 1, v_wantsRebuild_212_);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_220_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_243_; 
v_a_232_ = lean_ctor_get(v___x_219_, 0);
v_a_233_ = lean_ctor_get(v___x_219_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_243_ == 0)
{
v___x_235_ = v___x_219_;
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_inc(v_a_232_);
lean_dec(v___x_219_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v_a_233_);
v___x_238_ = v___x_216_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_trace_213_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_buildTime_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, sizeof(void*)*3, v_action_211_);
lean_ctor_set_uint8(v_reuseFailAlloc_242_, sizeof(void*)*3 + 1, v_wantsRebuild_212_);
v___x_238_ = v_reuseFailAlloc_242_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_232_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object* v_target_245_, lean_object* v_kind_246_, lean_object* v___x_247_, lean_object* v_data_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(v_target_245_, v_kind_246_, v___x_247_, v_data_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(lean_object* v_t_257_, lean_object* v_k_258_){
_start:
{
if (lean_obj_tag(v_t_257_) == 0)
{
lean_object* v_k_259_; lean_object* v_v_260_; lean_object* v_l_261_; lean_object* v_r_262_; uint8_t v___x_263_; 
v_k_259_ = lean_ctor_get(v_t_257_, 1);
v_v_260_ = lean_ctor_get(v_t_257_, 2);
v_l_261_ = lean_ctor_get(v_t_257_, 3);
v_r_262_ = lean_ctor_get(v_t_257_, 4);
v___x_263_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_258_, v_k_259_);
switch(v___x_263_)
{
case 0:
{
v_t_257_ = v_l_261_;
goto _start;
}
case 1:
{
lean_object* v___x_265_; 
lean_inc(v_v_260_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_v_260_);
return v___x_265_;
}
default: 
{
v_t_257_ = v_r_262_;
goto _start;
}
}
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(lean_object* v_t_268_, lean_object* v_k_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_268_, v_k_269_);
lean_dec(v_k_269_);
lean_dec(v_t_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(lean_object* v_package_271_, lean_object* v_as_272_, size_t v_sz_273_, size_t v_i_274_, lean_object* v_b_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_lt(v_i_274_, v_sz_273_);
if (v___x_276_ == 0)
{
return v_b_275_;
}
else
{
lean_object* v_a_277_; lean_object* v_baseName_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
lean_dec_ref(v_b_275_);
v_a_277_ = lean_array_uget_borrowed(v_as_272_, v_i_274_);
v_baseName_278_ = lean_ctor_get(v_a_277_, 1);
v___x_279_ = lean_box(0);
v___x_280_ = lean_name_eq(v_baseName_278_, v_package_271_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; size_t v___x_282_; size_t v___x_283_; 
v___x_281_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_274_, v___x_282_);
v_i_274_ = v___x_283_;
v_b_275_ = v___x_281_;
goto _start;
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc(v_a_277_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_a_277_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_279_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(lean_object* v_package_288_, lean_object* v_as_289_, lean_object* v_sz_290_, lean_object* v_i_291_, lean_object* v_b_292_){
_start:
{
size_t v_sz_boxed_293_; size_t v_i_boxed_294_; lean_object* v_res_295_; 
v_sz_boxed_293_ = lean_unbox_usize(v_sz_290_);
lean_dec(v_sz_290_);
v_i_boxed_294_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_res_295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_288_, v_as_289_, v_sz_boxed_293_, v_i_boxed_294_, v_b_292_);
lean_dec_ref(v_as_289_);
lean_dec(v_package_288_);
return v_res_295_;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2));
v___x_301_ = l_Lake_BuildTrace_nil(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_304_ = 0;
v___x_305_ = 0;
v___x_306_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0));
v___x_307_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_303_);
lean_ctor_set(v___x_307_, 2, v___x_302_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*3, v___x_305_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*3 + 1, v___x_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object* v_defaultPkg_318_, lean_object* v_root_319_, lean_object* v_self_320_, uint8_t v_facetless_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_a_330_; lean_object* v_a_331_; lean_object* v_a_334_; lean_object* v_a_335_; lean_object* v_a_338_; lean_object* v_a_339_; lean_object* v___x_341_; 
v___x_341_ = l_Lake_instDataKindModule;
switch(lean_obj_tag(v_self_320_))
{
case 0:
{
lean_object* v_module_342_; lean_object* v_toContext_343_; lean_object* v___x_344_; 
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_defaultPkg_318_);
v_module_342_ = lean_ctor_get(v_self_320_, 0);
lean_inc(v_module_342_);
lean_dec_ref(v_self_320_);
v_toContext_343_ = lean_ctor_get(v_a_326_, 1);
lean_inc(v_toContext_343_);
lean_dec_ref(v_a_326_);
lean_inc(v_module_342_);
v___x_344_ = l_Lake_Workspace_findModule_x3f(v_module_342_, v_toContext_343_);
lean_dec(v_toContext_343_);
if (lean_obj_tag(v___x_344_) == 1)
{
lean_object* v_val_345_; lean_object* v_lib_346_; lean_object* v_pkg_347_; lean_object* v_keyName_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_dec_ref(v_root_319_);
v_val_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___x_344_);
v_lib_346_ = lean_ctor_get(v_val_345_, 0);
v_pkg_347_ = lean_ctor_get(v_lib_346_, 0);
v_keyName_348_ = lean_ctor_get(v_pkg_347_, 2);
lean_inc(v_keyName_348_);
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v_keyName_348_);
lean_ctor_set(v___x_349_, 1, v_module_342_);
v___x_350_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_351_ = 0;
v___x_352_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_val_345_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_task_pure(v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_341_);
lean_ctor_set(v___x_355_, 2, v___x_350_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*3, v___x_351_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_349_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_a_327_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec(v___x_344_);
v___x_358_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_359_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
lean_dec_ref(v___x_359_);
v___x_361_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
v___x_363_ = 1;
v___x_364_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_342_, v___x_363_);
v___x_365_ = lean_string_append(v___x_362_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_366_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
v___x_368_ = 3;
v___x_369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*1, v___x_368_);
v___x_370_ = lean_array_get_size(v_a_327_);
v___x_371_ = lean_array_push(v_a_327_, v___x_369_);
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
case 1:
{
lean_object* v_package_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v_package_373_ = lean_ctor_get(v_self_320_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_self_320_);
if (v_isSharedCheck_436_ == 0)
{
v___x_375_ = v_self_320_;
v_isShared_376_ = v_isSharedCheck_436_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_package_373_);
lean_dec(v_self_320_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_436_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_a_378_; lean_object* v___x_393_; lean_object* v_a_395_; lean_object* v_a_396_; 
v___x_393_ = l_Lake_instDataKindPackage;
switch(lean_obj_tag(v_package_373_))
{
case 0:
{
lean_dec_ref(v_a_326_);
lean_dec_ref(v_root_319_);
v_a_395_ = v_defaultPkg_318_;
v_a_396_ = v_a_327_;
goto v___jp_394_;
}
case 2:
{
lean_object* v_toContext_409_; lean_object* v_packageMap_410_; lean_object* v___x_411_; 
lean_dec_ref(v_defaultPkg_318_);
v_toContext_409_ = lean_ctor_get(v_a_326_, 1);
lean_inc(v_toContext_409_);
lean_dec_ref(v_a_326_);
v_packageMap_410_ = lean_ctor_get(v_toContext_409_, 6);
lean_inc(v_packageMap_410_);
lean_dec(v_toContext_409_);
v___x_411_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_410_, v_package_373_);
lean_dec(v_packageMap_410_);
if (lean_obj_tag(v___x_411_) == 1)
{
lean_object* v_val_412_; 
lean_dec_ref(v_package_373_);
lean_dec_ref(v_root_319_);
v_val_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref(v___x_411_);
v_a_395_ = v_val_412_;
v_a_396_ = v_a_327_;
goto v___jp_394_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v___x_411_);
lean_del_object(v___x_375_);
v___x_413_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_414_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = 1;
v___x_419_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_373_, v___x_418_);
v___x_420_ = lean_string_append(v___x_417_, v___x_419_);
lean_dec_ref(v___x_419_);
v___x_421_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
v___x_423_ = 3;
v___x_424_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*1, v___x_423_);
v___x_425_ = lean_array_get_size(v_a_327_);
v___x_426_ = lean_array_push(v_a_327_, v___x_424_);
v_a_338_ = v___x_425_;
v_a_339_ = v___x_426_;
goto v___jp_337_;
}
}
default: 
{
lean_object* v_toContext_427_; lean_object* v_packages_428_; lean_object* v___x_429_; size_t v_sz_430_; size_t v___x_431_; lean_object* v___x_432_; lean_object* v_fst_433_; 
lean_dec_ref(v_defaultPkg_318_);
v_toContext_427_ = lean_ctor_get(v_a_326_, 1);
lean_inc(v_toContext_427_);
lean_dec_ref(v_a_326_);
v_packages_428_ = lean_ctor_get(v_toContext_427_, 5);
lean_inc_ref(v_packages_428_);
lean_dec(v_toContext_427_);
v___x_429_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_430_ = lean_array_size(v_packages_428_);
v___x_431_ = ((size_t)0ULL);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_373_, v_packages_428_, v_sz_430_, v___x_431_, v___x_429_);
lean_dec_ref(v_packages_428_);
v_fst_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_fst_433_);
lean_dec_ref(v___x_432_);
if (lean_obj_tag(v_fst_433_) == 0)
{
lean_del_object(v___x_375_);
v_a_378_ = v_a_327_;
goto v___jp_377_;
}
else
{
lean_object* v_val_434_; 
v_val_434_ = lean_ctor_get(v_fst_433_, 0);
lean_inc(v_val_434_);
lean_dec_ref(v_fst_433_);
if (lean_obj_tag(v_val_434_) == 1)
{
lean_object* v_val_435_; 
lean_dec(v_package_373_);
lean_dec_ref(v_root_319_);
v_val_435_ = lean_ctor_get(v_val_434_, 0);
lean_inc(v_val_435_);
lean_dec_ref(v_val_434_);
v_a_395_ = v_val_435_;
v_a_396_ = v_a_327_;
goto v___jp_394_;
}
else
{
lean_dec(v_val_434_);
lean_del_object(v___x_375_);
v_a_378_ = v_a_327_;
goto v___jp_377_;
}
}
}
}
v___jp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_379_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_380_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_381_ = lean_string_append(v___x_379_, v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
v___x_384_ = 1;
v___x_385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_373_, v___x_384_);
v___x_386_ = lean_string_append(v___x_383_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
v___x_389_ = 3;
v___x_390_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*1, v___x_389_);
v___x_391_ = lean_array_get_size(v_a_378_);
v___x_392_ = lean_array_push(v_a_378_, v___x_390_);
v_a_338_ = v___x_391_;
v_a_339_ = v___x_392_;
goto v___jp_337_;
}
v___jp_394_:
{
lean_object* v_keyName_397_; lean_object* v___x_399_; 
v_keyName_397_ = lean_ctor_get(v_a_395_, 2);
lean_inc(v_keyName_397_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v_keyName_397_);
v___x_399_ = v___x_375_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_keyName_397_);
v___x_399_ = v_reuseFailAlloc_408_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_400_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_401_ = 0;
v___x_402_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_a_395_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_task_pure(v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_393_);
lean_ctor_set(v___x_405_, 2, v___x_400_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*3, v___x_401_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_399_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_396_);
return v___x_407_;
}
}
}
}
case 2:
{
lean_object* v_package_437_; lean_object* v_module_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v_package_437_ = lean_ctor_get(v_self_320_, 0);
v_module_438_ = lean_ctor_get(v_self_320_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_self_320_);
if (v_isSharedCheck_523_ == 0)
{
v___x_440_ = v_self_320_;
v_isShared_441_ = v_isSharedCheck_523_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_module_438_);
lean_inc(v_package_437_);
lean_dec(v_self_320_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_523_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_a_443_; lean_object* v_a_444_; lean_object* v_a_481_; 
switch(lean_obj_tag(v_package_437_))
{
case 0:
{
lean_dec_ref(v_a_326_);
v_a_443_ = v_defaultPkg_318_;
v_a_444_ = v_a_327_;
goto v___jp_442_;
}
case 2:
{
lean_object* v_toContext_496_; lean_object* v_packageMap_497_; lean_object* v___x_498_; 
lean_dec_ref(v_defaultPkg_318_);
v_toContext_496_ = lean_ctor_get(v_a_326_, 1);
lean_inc(v_toContext_496_);
lean_dec_ref(v_a_326_);
v_packageMap_497_ = lean_ctor_get(v_toContext_496_, 6);
lean_inc(v_packageMap_497_);
lean_dec(v_toContext_496_);
v___x_498_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_497_, v_package_437_);
lean_dec(v_packageMap_497_);
if (lean_obj_tag(v___x_498_) == 1)
{
lean_object* v_val_499_; 
lean_dec_ref(v_package_437_);
v_val_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref(v___x_498_);
v_a_443_ = v_val_499_;
v_a_444_ = v_a_327_;
goto v___jp_442_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v___x_498_);
lean_del_object(v___x_440_);
lean_dec(v_module_438_);
v___x_500_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_501_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_502_ = lean_string_append(v___x_500_, v___x_501_);
lean_dec_ref(v___x_501_);
v___x_503_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_504_ = lean_string_append(v___x_502_, v___x_503_);
v___x_505_ = 1;
v___x_506_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_437_, v___x_505_);
v___x_507_ = lean_string_append(v___x_504_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_509_ = lean_string_append(v___x_507_, v___x_508_);
v___x_510_ = 3;
v___x_511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*1, v___x_510_);
v___x_512_ = lean_array_get_size(v_a_327_);
v___x_513_ = lean_array_push(v_a_327_, v___x_511_);
v_a_334_ = v___x_512_;
v_a_335_ = v___x_513_;
goto v___jp_333_;
}
}
default: 
{
lean_object* v_toContext_514_; lean_object* v_packages_515_; lean_object* v___x_516_; size_t v_sz_517_; size_t v___x_518_; lean_object* v___x_519_; lean_object* v_fst_520_; 
lean_dec_ref(v_defaultPkg_318_);
v_toContext_514_ = lean_ctor_get(v_a_326_, 1);
lean_inc(v_toContext_514_);
lean_dec_ref(v_a_326_);
v_packages_515_ = lean_ctor_get(v_toContext_514_, 5);
lean_inc_ref(v_packages_515_);
lean_dec(v_toContext_514_);
v___x_516_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_517_ = lean_array_size(v_packages_515_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_437_, v_packages_515_, v_sz_517_, v___x_518_, v___x_516_);
lean_dec_ref(v_packages_515_);
v_fst_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_fst_520_);
lean_dec_ref(v___x_519_);
if (lean_obj_tag(v_fst_520_) == 0)
{
lean_del_object(v___x_440_);
lean_dec(v_module_438_);
v_a_481_ = v_a_327_;
goto v___jp_480_;
}
else
{
lean_object* v_val_521_; 
v_val_521_ = lean_ctor_get(v_fst_520_, 0);
lean_inc(v_val_521_);
lean_dec_ref(v_fst_520_);
if (lean_obj_tag(v_val_521_) == 1)
{
lean_object* v_val_522_; 
lean_dec(v_package_437_);
v_val_522_ = lean_ctor_get(v_val_521_, 0);
lean_inc(v_val_522_);
lean_dec_ref(v_val_521_);
v_a_443_ = v_val_522_;
v_a_444_ = v_a_327_;
goto v___jp_442_;
}
else
{
lean_dec(v_val_521_);
lean_del_object(v___x_440_);
lean_dec(v_module_438_);
v_a_481_ = v_a_327_;
goto v___jp_480_;
}
}
}
}
v___jp_442_:
{
lean_object* v___x_445_; 
lean_inc_ref(v_a_443_);
lean_inc(v_module_438_);
v___x_445_ = l_Lake_Package_findTargetModule_x3f(v_module_438_, v_a_443_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_val_446_; lean_object* v_keyName_447_; lean_object* v___x_449_; 
lean_dec_ref(v_root_319_);
v_val_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v___x_445_);
v_keyName_447_ = lean_ctor_get(v_a_443_, 2);
lean_inc(v_keyName_447_);
lean_dec_ref(v_a_443_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_keyName_447_);
v___x_449_ = v___x_440_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_keyName_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_module_438_);
v___x_449_ = v_reuseFailAlloc_458_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_450_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_451_ = 0;
v___x_452_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_val_446_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_task_pure(v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_341_);
lean_ctor_set(v___x_455_, 2, v___x_450_);
lean_ctor_set_uint8(v___x_455_, sizeof(void*)*3, v___x_451_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_449_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_a_444_);
return v___x_457_;
}
}
else
{
lean_object* v_baseName_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_445_);
lean_del_object(v___x_440_);
v_baseName_459_ = lean_ctor_get(v_a_443_, 1);
lean_inc(v_baseName_459_);
lean_dec_ref(v_a_443_);
v___x_460_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_461_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6));
v___x_464_ = lean_string_append(v___x_462_, v___x_463_);
v___x_465_ = 1;
v___x_466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_438_, v___x_465_);
v___x_467_ = lean_string_append(v___x_464_, v___x_466_);
lean_dec_ref(v___x_466_);
v___x_468_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
v___x_470_ = 0;
v___x_471_ = l_Lean_Name_toString(v_baseName_459_, v___x_470_);
v___x_472_ = lean_string_append(v___x_469_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v___x_475_ = 3;
v___x_476_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*1, v___x_475_);
v___x_477_ = lean_array_get_size(v_a_444_);
v___x_478_ = lean_array_push(v_a_444_, v___x_476_);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
}
v___jp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_482_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_483_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
v___x_487_ = 1;
v___x_488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_437_, v___x_487_);
v___x_489_ = lean_string_append(v___x_486_, v___x_488_);
lean_dec_ref(v___x_488_);
v___x_490_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_491_ = lean_string_append(v___x_489_, v___x_490_);
v___x_492_ = 3;
v___x_493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*1, v___x_492_);
v___x_494_ = lean_array_get_size(v_a_481_);
v___x_495_ = lean_array_push(v_a_481_, v___x_493_);
v_a_334_ = v___x_494_;
v_a_335_ = v___x_495_;
goto v___jp_333_;
}
}
}
case 3:
{
lean_object* v_package_524_; lean_object* v_target_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_675_; 
v_package_524_ = lean_ctor_get(v_self_320_, 0);
v_target_525_ = lean_ctor_get(v_self_320_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_self_320_);
if (v_isSharedCheck_675_ == 0)
{
v___x_527_ = v_self_320_;
v_isShared_528_ = v_isSharedCheck_675_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_target_525_);
lean_inc(v_package_524_);
lean_dec(v_self_320_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_675_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_a_530_; lean_object* v_a_531_; lean_object* v_a_633_; 
switch(lean_obj_tag(v_package_524_))
{
case 0:
{
v_a_530_ = v_defaultPkg_318_;
v_a_531_ = v_a_327_;
goto v___jp_529_;
}
case 2:
{
lean_object* v_toContext_648_; lean_object* v_packageMap_649_; lean_object* v___x_650_; 
lean_dec_ref(v_defaultPkg_318_);
v_toContext_648_ = lean_ctor_get(v_a_326_, 1);
v_packageMap_649_ = lean_ctor_get(v_toContext_648_, 6);
v___x_650_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_649_, v_package_524_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; 
lean_dec_ref(v_package_524_);
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref(v___x_650_);
v_a_530_ = v_val_651_;
v_a_531_ = v_a_327_;
goto v___jp_529_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v___x_650_);
lean_del_object(v___x_527_);
lean_dec(v_target_525_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v___x_652_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_653_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
v___x_657_ = 1;
v___x_658_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_524_, v___x_657_);
v___x_659_ = lean_string_append(v___x_656_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
v___x_662_ = 3;
v___x_663_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*1, v___x_662_);
v___x_664_ = lean_array_get_size(v_a_327_);
v___x_665_ = lean_array_push(v_a_327_, v___x_663_);
v_a_330_ = v___x_664_;
v_a_331_ = v___x_665_;
goto v___jp_329_;
}
}
default: 
{
lean_object* v_toContext_666_; lean_object* v_packages_667_; lean_object* v___x_668_; size_t v_sz_669_; size_t v___x_670_; lean_object* v___x_671_; lean_object* v_fst_672_; 
lean_dec_ref(v_defaultPkg_318_);
v_toContext_666_ = lean_ctor_get(v_a_326_, 1);
v_packages_667_ = lean_ctor_get(v_toContext_666_, 5);
v___x_668_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
v_sz_669_ = lean_array_size(v_packages_667_);
v___x_670_ = ((size_t)0ULL);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_524_, v_packages_667_, v_sz_669_, v___x_670_, v___x_668_);
v_fst_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_fst_672_);
lean_dec_ref(v___x_671_);
if (lean_obj_tag(v_fst_672_) == 0)
{
lean_del_object(v___x_527_);
lean_dec(v_target_525_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v_a_633_ = v_a_327_;
goto v___jp_632_;
}
else
{
lean_object* v_val_673_; 
v_val_673_ = lean_ctor_get(v_fst_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v_fst_672_);
if (lean_obj_tag(v_val_673_) == 1)
{
lean_object* v_val_674_; 
lean_dec(v_package_524_);
v_val_674_ = lean_ctor_get(v_val_673_, 0);
lean_inc(v_val_674_);
lean_dec_ref(v_val_673_);
v_a_530_ = v_val_674_;
v_a_531_ = v_a_327_;
goto v___jp_529_;
}
else
{
lean_dec(v_val_673_);
lean_del_object(v___x_527_);
lean_dec(v_target_525_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v_a_633_ = v_a_327_;
goto v___jp_632_;
}
}
}
}
v___jp_529_:
{
lean_object* v_baseName_532_; lean_object* v_keyName_533_; lean_object* v___x_535_; 
v_baseName_532_ = lean_ctor_get(v_a_530_, 1);
v_keyName_533_ = lean_ctor_get(v_a_530_, 2);
lean_inc(v_target_525_);
lean_inc(v_keyName_533_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v_keyName_533_);
v___x_535_ = v___x_527_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_keyName_533_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_target_525_);
v___x_535_ = v_reuseFailAlloc_631_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
if (v_facetless_321_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v_root_319_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_530_);
lean_ctor_set(v___x_536_, 1, v_target_525_);
v___x_537_ = lean_apply_7(v_a_322_, v___x_536_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_531_, lean_box(0));
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_a_539_ = lean_ctor_get(v___x_537_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v___x_537_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_535_);
lean_ctor_set(v___x_543_, 1, v_a_538_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_a_539_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v___x_535_);
v_a_548_ = lean_ctor_get(v___x_537_, 0);
v_a_549_ = lean_ctor_get(v___x_537_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_537_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_inc(v_a_548_);
lean_dec(v___x_537_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_548_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v___x_557_; 
v___x_557_ = l_Lake_Package_findTargetDecl_x3f(v_target_525_, v_a_530_);
if (lean_obj_tag(v___x_557_) == 1)
{
lean_object* v_val_558_; lean_object* v_name_559_; lean_object* v_kind_560_; lean_object* v_config_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_root_319_);
v_val_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_val_558_);
lean_dec_ref(v___x_557_);
v_name_559_ = lean_ctor_get(v_val_558_, 1);
v_kind_560_ = lean_ctor_get(v_val_558_, 2);
v_config_561_ = lean_ctor_get(v_val_558_, 3);
v_isSharedCheck_614_ = !lean_is_exclusive(v_val_558_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_val_558_, 0);
lean_dec(v_unused_615_);
v___x_563_ = v_val_558_;
v_isShared_564_ = v_isSharedCheck_614_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_config_561_);
lean_inc(v_kind_560_);
lean_inc(v_name_559_);
lean_dec(v_val_558_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_614_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint8_t v___x_565_; 
v___x_565_ = l_Lean_Name_isAnonymous(v_kind_560_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_target_525_);
v___x_566_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9));
lean_inc(v_kind_560_);
v___x_567_ = l_Lean_Name_str___override(v_kind_560_, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_568_, 0, v_a_530_);
lean_ctor_set(v___x_568_, 1, v_name_559_);
lean_ctor_set(v___x_568_, 2, v_config_561_);
lean_inc(v___x_567_);
lean_inc_ref(v___x_535_);
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 1);
lean_ctor_set(v___x_563_, 3, v___x_567_);
lean_ctor_set(v___x_563_, 2, v___x_568_);
lean_ctor_set(v___x_563_, 1, v_kind_560_);
lean_ctor_set(v___x_563_, 0, v___x_535_);
v___x_570_ = v___x_563_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_kind_560_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_592_, 3, v___x_567_);
v___x_570_ = v_reuseFailAlloc_592_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_apply_7(v_a_322_, v___x_570_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_531_, lean_box(0));
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_582_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_a_573_ = lean_ctor_get(v___x_571_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_582_ == 0)
{
v___x_575_ = v___x_571_;
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_582_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_535_);
lean_ctor_set(v___x_577_, 1, v___x_567_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_a_572_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_578_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_a_573_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v___x_567_);
lean_dec_ref(v___x_535_);
v_a_583_ = lean_ctor_get(v___x_571_, 0);
v_a_584_ = lean_ctor_get(v___x_571_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_571_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_inc(v_a_583_);
lean_dec(v___x_571_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_583_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_563_);
lean_dec(v_config_561_);
lean_dec(v_kind_560_);
lean_dec(v_name_559_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_a_530_);
lean_ctor_set(v___x_593_, 1, v_target_525_);
v___x_594_ = lean_apply_7(v_a_322_, v___x_593_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_531_, lean_box(0));
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_a_596_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_604_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_535_);
lean_ctor_set(v___x_600_, 1, v_a_595_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_a_596_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v___x_535_);
v_a_605_ = lean_ctor_get(v___x_594_, 0);
v_a_606_ = lean_ctor_get(v___x_594_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_594_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_inc(v_a_605_);
lean_dec(v___x_594_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_605_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc(v_baseName_532_);
lean_dec(v___x_557_);
lean_dec_ref(v___x_535_);
lean_dec_ref(v_a_530_);
lean_dec(v_target_525_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v___x_616_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_617_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_618_ = lean_string_append(v___x_616_, v___x_617_);
lean_dec_ref(v___x_617_);
v___x_619_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10));
v___x_620_ = lean_string_append(v___x_618_, v___x_619_);
v___x_621_ = 0;
v___x_622_ = l_Lean_Name_toString(v_baseName_532_, v___x_621_);
v___x_623_ = lean_string_append(v___x_620_, v___x_622_);
lean_dec_ref(v___x_622_);
v___x_624_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_625_ = lean_string_append(v___x_623_, v___x_624_);
v___x_626_ = 3;
v___x_627_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_626_);
v___x_628_ = lean_array_get_size(v_a_531_);
v___x_629_ = lean_array_push(v_a_531_, v___x_627_);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
return v___x_630_;
}
}
}
}
v___jp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_634_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_635_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_636_ = lean_string_append(v___x_634_, v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_638_ = lean_string_append(v___x_636_, v___x_637_);
v___x_639_ = 1;
v___x_640_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_524_, v___x_639_);
v___x_641_ = lean_string_append(v___x_638_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
v___x_644_ = 3;
v___x_645_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*1, v___x_644_);
v___x_646_ = lean_array_get_size(v_a_633_);
v___x_647_ = lean_array_push(v_a_633_, v___x_645_);
v_a_330_ = v___x_646_;
v_a_331_ = v___x_647_;
goto v___jp_329_;
}
}
}
default: 
{
lean_object* v_target_676_; lean_object* v_facet_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_747_; 
v_target_676_ = lean_ctor_get(v_self_320_, 0);
v_facet_677_ = lean_ctor_get(v_self_320_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_self_320_);
if (v_isSharedCheck_747_ == 0)
{
v___x_679_ = v_self_320_;
v_isShared_680_ = v_isSharedCheck_747_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_facet_677_);
lean_inc(v_target_676_);
lean_dec(v_self_320_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_747_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
uint8_t v___x_681_; lean_object* v___x_682_; 
v___x_681_ = 0;
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
lean_inc(v_a_323_);
lean_inc_ref(v_a_322_);
lean_inc_ref(v_target_676_);
lean_inc_ref(v_root_319_);
v___x_682_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_318_, v_root_319_, v_target_676_, v___x_681_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_745_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
v_snd_684_ = lean_ctor_get(v_a_683_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_a_683_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v_a_683_, 0);
lean_dec(v_unused_746_);
v___x_686_ = v_a_683_;
v_isShared_687_ = v_isSharedCheck_745_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_dec(v_a_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_745_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_743_; 
v_a_688_ = lean_ctor_get(v___x_682_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_682_, 0);
lean_dec(v_unused_744_);
v___x_690_ = v___x_682_;
v_isShared_691_ = v_isSharedCheck_743_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_682_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_743_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_kind_692_; lean_object* v___y_694_; uint8_t v___x_730_; 
v_kind_692_ = lean_ctor_get(v_snd_684_, 1);
v___x_730_ = l_Lean_Name_isAnonymous(v_kind_692_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Lean_Name_isAnonymous(v_facet_677_);
if (v___x_731_ == 0)
{
v___y_694_ = v_facet_677_;
goto v___jp_693_;
}
else
{
lean_object* v___x_732_; 
lean_dec(v_facet_677_);
v___x_732_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12));
v___y_694_ = v___x_732_;
goto v___jp_693_;
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_del_object(v___x_690_);
lean_del_object(v___x_686_);
lean_dec(v_snd_684_);
lean_del_object(v___x_679_);
lean_dec(v_facet_677_);
lean_dec_ref(v_target_676_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v___x_733_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_734_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_735_ = lean_string_append(v___x_733_, v___x_734_);
lean_dec_ref(v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
v___x_737_ = lean_string_append(v___x_735_, v___x_736_);
v___x_738_ = 3;
v___x_739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set_uint8(v___x_739_, sizeof(void*)*1, v___x_738_);
v___x_740_ = lean_array_get_size(v_a_688_);
v___x_741_ = lean_array_push(v_a_688_, v___x_739_);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
return v___x_742_;
}
v___jp_693_:
{
lean_object* v_toContext_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_toContext_695_ = lean_ctor_get(v_a_326_, 1);
lean_inc(v_kind_692_);
v___x_696_ = l_Lean_Name_append(v_kind_692_, v___y_694_);
v___x_697_ = l_Lake_Workspace_findFacetConfig_x3f(v___x_696_, v_toContext_695_);
if (lean_obj_tag(v___x_697_) == 1)
{
lean_object* v_val_698_; lean_object* v_outKind_699_; lean_object* v___f_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec_ref(v_root_319_);
v_val_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v___x_697_);
v_outKind_699_ = lean_ctor_get(v_val_698_, 2);
lean_inc(v_outKind_699_);
lean_dec(v_val_698_);
lean_inc(v___x_696_);
lean_inc(v_kind_692_);
lean_inc_ref(v_target_676_);
v___f_700_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 11, 3);
lean_closure_set(v___f_700_, 0, v_target_676_);
lean_closure_set(v___f_700_, 1, v_kind_692_);
lean_closure_set(v___f_700_, 2, v___x_696_);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_703_ = l_Lake_Job_bindM___redArg(v_outKind_699_, v_snd_684_, v___f_700_, v___x_701_, v___x_681_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v___x_702_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___x_696_);
v___x_705_ = v___x_679_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_target_676_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_696_);
v___x_705_ = v_reuseFailAlloc_712_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_703_);
lean_ctor_set(v___x_686_, 0, v___x_705_);
v___x_707_ = v___x_686_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_703_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_707_);
v___x_709_ = v___x_690_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_a_688_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
lean_dec(v___x_697_);
lean_del_object(v___x_686_);
lean_dec(v_snd_684_);
lean_del_object(v___x_679_);
lean_dec_ref(v_target_676_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
v___x_713_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_714_ = l_Lake_PartialBuildKey_toString(v_root_319_);
v___x_715_ = lean_string_append(v___x_713_, v___x_714_);
lean_dec_ref(v___x_714_);
v___x_716_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
v___x_717_ = lean_string_append(v___x_715_, v___x_716_);
v___x_718_ = 1;
v___x_719_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_696_, v___x_718_);
v___x_720_ = lean_string_append(v___x_717_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_722_ = lean_string_append(v___x_720_, v___x_721_);
v___x_723_ = 3;
v___x_724_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*1, v___x_723_);
v___x_725_ = lean_array_get_size(v_a_688_);
v___x_726_ = lean_array_push(v_a_688_, v___x_724_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 1);
lean_ctor_set(v___x_690_, 1, v___x_726_);
lean_ctor_set(v___x_690_, 0, v___x_725_);
v___x_728_ = v___x_690_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_679_);
lean_dec(v_facet_677_);
lean_dec_ref(v_target_676_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_root_319_);
return v___x_682_;
}
}
}
}
v___jp_329_:
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v_a_330_);
lean_ctor_set(v___x_332_, 1, v_a_331_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_336_; 
v___x_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_336_, 0, v_a_334_);
lean_ctor_set(v___x_336_, 1, v_a_335_);
return v___x_336_;
}
v___jp_337_:
{
lean_object* v___x_340_; 
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v_a_338_);
lean_ctor_set(v___x_340_, 1, v_a_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object* v_defaultPkg_748_, lean_object* v_root_749_, lean_object* v_self_750_, lean_object* v_facetless_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
uint8_t v_facetless_boxed_759_; lean_object* v_res_760_; 
v_facetless_boxed_759_ = lean_unbox(v_facetless_751_);
v_res_760_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_748_, v_root_749_, v_self_750_, v_facetless_boxed_759_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(lean_object* v_00_u03b2_761_, lean_object* v_inst_762_, lean_object* v_t_763_, lean_object* v_k_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_763_, v_k_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(lean_object* v_00_u03b2_766_, lean_object* v_inst_767_, lean_object* v_t_768_, lean_object* v_k_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(v_00_u03b2_766_, v_inst_767_, v_t_768_, v_k_769_);
lean_dec(v_k_769_);
lean_dec(v_t_768_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object* v_defaultPkg_771_, lean_object* v_self_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
uint8_t v___x_780_; lean_object* v___x_781_; 
v___x_780_ = 1;
lean_inc_ref(v_self_772_);
v___x_781_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_771_, v_self_772_, v_self_772_, v___x_780_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore___boxed(lean_object* v_defaultPkg_782_, lean_object* v_self_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lake_PartialBuildKey_fetchInCore(v_defaultPkg_782_, v_self_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object* v_defaultPkg_792_, lean_object* v_self_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
uint8_t v___x_801_; lean_object* v___x_802_; 
v___x_801_ = 1;
lean_inc_ref(v_self_793_);
v___x_802_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_792_, v_self_793_, v_self_793_, v___x_801_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_813_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_a_804_ = lean_ctor_get(v___x_802_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_813_ == 0)
{
v___x_806_ = v___x_802_;
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_snd_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v_snd_808_ = lean_ctor_get(v_a_803_, 1);
lean_inc(v_snd_808_);
lean_dec(v_a_803_);
v___x_809_ = l_Lake_Job_toOpaque___redArg(v_snd_808_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_a_804_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v_a_814_ = lean_ctor_get(v___x_802_, 0);
v_a_815_ = lean_ctor_get(v___x_802_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_802_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_inc(v_a_814_);
lean_dec(v___x_802_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_814_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn___boxed(lean_object* v_defaultPkg_823_, lean_object* v_self_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lake_PartialBuildKey_fetchIn(v_defaultPkg_823_, v_self_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(lean_object* v_target_833_, lean_object* v_kind_834_, lean_object* v_facet_835_, lean_object* v_data_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_log_844_; uint8_t v_action_845_; uint8_t v_wantsRebuild_846_; lean_object* v_trace_847_; lean_object* v_buildTime_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_878_; 
v_log_844_ = lean_ctor_get(v___y_842_, 0);
v_action_845_ = lean_ctor_get_uint8(v___y_842_, sizeof(void*)*3);
v_wantsRebuild_846_ = lean_ctor_get_uint8(v___y_842_, sizeof(void*)*3 + 1);
v_trace_847_ = lean_ctor_get(v___y_842_, 1);
v_buildTime_848_ = lean_ctor_get(v___y_842_, 2);
v_isSharedCheck_878_ = !lean_is_exclusive(v___y_842_);
if (v_isSharedCheck_878_ == 0)
{
v___x_850_ = v___y_842_;
v_isShared_851_ = v_isSharedCheck_878_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_buildTime_848_);
lean_inc(v_trace_847_);
lean_inc(v_log_844_);
lean_dec(v___y_842_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_878_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_852_, 0, v_target_833_);
lean_ctor_set(v___x_852_, 1, v_kind_834_);
lean_ctor_set(v___x_852_, 2, v_data_836_);
lean_ctor_set(v___x_852_, 3, v_facet_835_);
v___x_853_ = lean_apply_7(v___y_837_, v___x_852_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v_log_844_, lean_box(0));
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_865_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_a_855_ = lean_ctor_get(v___x_853_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_865_ == 0)
{
v___x_857_ = v___x_853_;
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_865_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v_a_855_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_855_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_trace_847_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_buildTime_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_864_, sizeof(void*)*3, v_action_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_864_, sizeof(void*)*3 + 1, v_wantsRebuild_846_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_854_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_877_; 
v_a_866_ = lean_ctor_get(v___x_853_, 0);
v_a_867_ = lean_ctor_get(v___x_853_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_877_ == 0)
{
v___x_869_ = v___x_853_;
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_inc(v_a_866_);
lean_dec(v___x_853_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v_a_867_);
v___x_872_ = v___x_850_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_trace_847_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_buildTime_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*3, v_action_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*3 + 1, v_wantsRebuild_846_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v___x_872_);
v___x_874_ = v___x_869_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_866_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed(lean_object* v_target_879_, lean_object* v_kind_880_, lean_object* v_facet_881_, lean_object* v_data_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(v_target_879_, v_kind_880_, v_facet_881_, v_data_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(lean_object* v_root_891_, lean_object* v_self_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lake_instDataKindModule;
switch(lean_obj_tag(v_self_892_))
{
case 0:
{
lean_object* v_module_901_; lean_object* v_toContext_902_; lean_object* v___x_903_; 
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
v_module_901_ = lean_ctor_get(v_self_892_, 0);
lean_inc(v_module_901_);
lean_dec_ref(v_self_892_);
v_toContext_902_ = lean_ctor_get(v_a_897_, 1);
lean_inc(v_toContext_902_);
lean_dec_ref(v_a_897_);
lean_inc(v_module_901_);
v___x_903_ = l_Lake_Workspace_findModule_x3f(v_module_901_, v_toContext_902_);
lean_dec(v_toContext_902_);
if (lean_obj_tag(v___x_903_) == 1)
{
lean_object* v_val_904_; lean_object* v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec(v_module_901_);
lean_dec_ref(v_root_891_);
v_val_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v___x_903_);
v___x_905_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_906_ = 0;
v___x_907_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_val_904_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_task_pure(v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v___x_900_);
lean_ctor_set(v___x_910_, 2, v___x_905_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*3, v___x_906_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_a_898_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v___x_903_);
v___x_912_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_913_ = l_Lake_BuildKey_toString(v_root_891_);
v___x_914_ = lean_string_append(v___x_912_, v___x_913_);
lean_dec_ref(v___x_913_);
v___x_915_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_916_ = lean_string_append(v___x_914_, v___x_915_);
v___x_917_ = 1;
v___x_918_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_901_, v___x_917_);
v___x_919_ = lean_string_append(v___x_916_, v___x_918_);
lean_dec_ref(v___x_918_);
v___x_920_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_921_ = lean_string_append(v___x_919_, v___x_920_);
v___x_922_ = 3;
v___x_923_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*1, v___x_922_);
v___x_924_ = lean_array_get_size(v_a_898_);
v___x_925_ = lean_array_push(v_a_898_, v___x_923_);
v___x_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
return v___x_926_;
}
}
case 1:
{
lean_object* v_toContext_927_; lean_object* v_package_928_; lean_object* v_packageMap_929_; lean_object* v___x_930_; 
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
v_toContext_927_ = lean_ctor_get(v_a_897_, 1);
lean_inc(v_toContext_927_);
lean_dec_ref(v_a_897_);
v_package_928_ = lean_ctor_get(v_self_892_, 0);
lean_inc(v_package_928_);
lean_dec_ref(v_self_892_);
v_packageMap_929_ = lean_ctor_get(v_toContext_927_, 6);
lean_inc(v_packageMap_929_);
lean_dec(v_toContext_927_);
v___x_930_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_929_, v_package_928_);
lean_dec(v_packageMap_929_);
if (lean_obj_tag(v___x_930_) == 1)
{
lean_object* v_val_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v_package_928_);
lean_dec_ref(v_root_891_);
v_val_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_val_931_);
lean_dec_ref(v___x_930_);
v___x_932_ = l_Lake_instDataKindPackage;
v___x_933_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_934_ = 0;
v___x_935_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_val_931_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_task_pure(v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_932_);
lean_ctor_set(v___x_938_, 2, v___x_933_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*3, v___x_934_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_a_898_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v___x_930_);
v___x_940_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_941_ = l_Lake_BuildKey_toString(v_root_891_);
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
v___x_945_ = 1;
v___x_946_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_928_, v___x_945_);
v___x_947_ = lean_string_append(v___x_944_, v___x_946_);
lean_dec_ref(v___x_946_);
v___x_948_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
v___x_950_ = 3;
v___x_951_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_950_);
v___x_952_ = lean_array_get_size(v_a_898_);
v___x_953_ = lean_array_push(v_a_898_, v___x_951_);
v___x_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
return v___x_954_;
}
}
case 2:
{
lean_object* v_toContext_955_; lean_object* v_package_956_; lean_object* v_module_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
v_toContext_955_ = lean_ctor_get(v_a_897_, 1);
lean_inc(v_toContext_955_);
lean_dec_ref(v_a_897_);
v_package_956_ = lean_ctor_get(v_self_892_, 0);
v_module_957_ = lean_ctor_get(v_self_892_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_self_892_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_959_ = v_self_892_;
v_isShared_960_ = v_isSharedCheck_1015_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_module_957_);
lean_inc(v_package_956_);
lean_dec(v_self_892_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1015_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_packageMap_961_; lean_object* v___x_962_; 
v_packageMap_961_ = lean_ctor_get(v_toContext_955_, 6);
lean_inc(v_packageMap_961_);
lean_dec(v_toContext_955_);
v___x_962_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_961_, v_package_956_);
lean_dec(v_packageMap_961_);
if (lean_obj_tag(v___x_962_) == 1)
{
lean_object* v_val_963_; lean_object* v___x_964_; 
lean_dec(v_package_956_);
v_val_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc(v_val_963_);
lean_dec_ref(v___x_962_);
lean_inc(v_val_963_);
lean_inc(v_module_957_);
v___x_964_ = l_Lake_Package_findTargetModule_x3f(v_module_957_, v_val_963_);
if (lean_obj_tag(v___x_964_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec(v_val_963_);
lean_dec(v_module_957_);
lean_dec_ref(v_root_891_);
v_val_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_val_965_);
lean_dec_ref(v___x_964_);
v___x_966_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
v___x_967_ = 0;
v___x_968_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 0);
lean_ctor_set(v___x_959_, 1, v___x_968_);
lean_ctor_set(v___x_959_, 0, v_val_965_);
v___x_970_ = v___x_959_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_val_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_974_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_task_pure(v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_900_);
lean_ctor_set(v___x_972_, 2, v___x_966_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*3, v___x_967_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v_a_898_);
return v___x_973_;
}
}
else
{
lean_object* v_baseName_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
lean_dec(v___x_964_);
v_baseName_975_ = lean_ctor_get(v_val_963_, 1);
lean_inc(v_baseName_975_);
lean_dec(v_val_963_);
v___x_976_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_977_ = l_Lake_BuildKey_toString(v_root_891_);
v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
lean_dec_ref(v___x_977_);
v___x_979_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
v___x_980_ = lean_string_append(v___x_978_, v___x_979_);
v___x_981_ = 1;
v___x_982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_957_, v___x_981_);
v___x_983_ = lean_string_append(v___x_980_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___x_986_ = 0;
v___x_987_ = l_Lean_Name_toString(v_baseName_975_, v___x_986_);
v___x_988_ = lean_string_append(v___x_985_, v___x_987_);
lean_dec_ref(v___x_987_);
v___x_989_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
v___x_991_ = 3;
v___x_992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*1, v___x_991_);
v___x_993_ = lean_array_get_size(v_a_898_);
v___x_994_ = lean_array_push(v_a_898_, v___x_992_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 1, v___x_994_);
lean_ctor_set(v___x_959_, 0, v___x_993_);
v___x_996_ = v___x_959_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_dec(v___x_962_);
lean_dec(v_module_957_);
v___x_998_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_999_ = l_Lake_BuildKey_toString(v_root_891_);
v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_1002_ = lean_string_append(v___x_1000_, v___x_1001_);
v___x_1003_ = 1;
v___x_1004_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_956_, v___x_1003_);
v___x_1005_ = lean_string_append(v___x_1002_, v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
v___x_1008_ = 3;
v___x_1009_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*1, v___x_1008_);
v___x_1010_ = lean_array_get_size(v_a_898_);
v___x_1011_ = lean_array_push(v_a_898_, v___x_1009_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
lean_ctor_set(v___x_959_, 1, v___x_1011_);
lean_ctor_set(v___x_959_, 0, v___x_1010_);
v___x_1013_ = v___x_959_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
case 3:
{
lean_object* v_toContext_1016_; lean_object* v_package_1017_; lean_object* v_target_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1046_; 
v_toContext_1016_ = lean_ctor_get(v_a_897_, 1);
v_package_1017_ = lean_ctor_get(v_self_892_, 0);
v_target_1018_ = lean_ctor_get(v_self_892_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_self_892_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1020_ = v_self_892_;
v_isShared_1021_ = v_isSharedCheck_1046_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_target_1018_);
lean_inc(v_package_1017_);
lean_dec(v_self_892_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1046_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_packageMap_1022_; lean_object* v___x_1023_; 
v_packageMap_1022_ = lean_ctor_get(v_toContext_1016_, 6);
v___x_1023_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_1022_, v_package_1017_);
if (lean_obj_tag(v___x_1023_) == 1)
{
lean_object* v_val_1024_; lean_object* v___x_1026_; 
lean_dec(v_package_1017_);
lean_dec_ref(v_root_891_);
v_val_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref(v___x_1023_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
lean_ctor_set(v___x_1020_, 0, v_val_1024_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_val_1024_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_target_1018_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_apply_7(v_a_893_, v___x_1026_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, lean_box(0));
return v___x_1027_;
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v___x_1023_);
lean_dec(v_target_1018_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
v___x_1029_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1030_ = l_Lake_BuildKey_toString(v_root_891_);
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___x_1034_ = 1;
v___x_1035_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_package_1017_, v___x_1034_);
v___x_1036_ = lean_string_append(v___x_1033_, v___x_1035_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
v___x_1038_ = lean_string_append(v___x_1036_, v___x_1037_);
v___x_1039_ = 3;
v___x_1040_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set_uint8(v___x_1040_, sizeof(void*)*1, v___x_1039_);
v___x_1041_ = lean_array_get_size(v_a_898_);
v___x_1042_ = lean_array_push(v_a_898_, v___x_1040_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
lean_ctor_set(v___x_1020_, 1, v___x_1042_);
lean_ctor_set(v___x_1020_, 0, v___x_1041_);
v___x_1044_ = v___x_1020_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
default: 
{
lean_object* v_target_1047_; lean_object* v_facet_1048_; lean_object* v___x_1049_; 
v_target_1047_ = lean_ctor_get(v_self_892_, 0);
v_facet_1048_ = lean_ctor_get(v_self_892_, 1);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc(v_a_895_);
lean_inc(v_a_894_);
lean_inc_ref(v_a_893_);
lean_inc_ref(v_target_1047_);
lean_inc_ref(v_root_891_);
v___x_1049_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_root_891_, v_target_1047_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1097_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_a_1051_ = lean_ctor_get(v___x_1049_, 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1053_ = v___x_1049_;
v_isShared_1054_ = v_isSharedCheck_1097_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1097_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_kind_1055_; uint8_t v___x_1056_; 
v_kind_1055_ = lean_ctor_get(v_a_1050_, 1);
v___x_1056_ = l_Lean_Name_isAnonymous(v_kind_1055_);
if (v___x_1056_ == 0)
{
lean_object* v_toContext_1057_; lean_object* v___x_1058_; 
lean_inc(v_facet_1048_);
lean_inc_ref(v_target_1047_);
lean_dec_ref(v_self_892_);
v_toContext_1057_ = lean_ctor_get(v_a_897_, 1);
v___x_1058_ = l_Lake_Workspace_findFacetConfig_x3f(v_facet_1048_, v_toContext_1057_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v_outKind_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_dec_ref(v_root_891_);
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_val_1059_);
lean_dec_ref(v___x_1058_);
v_outKind_1060_ = lean_ctor_get(v_val_1059_, 2);
lean_inc(v_outKind_1060_);
lean_dec(v_val_1059_);
lean_inc(v_kind_1055_);
v___f_1061_ = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed), 11, 3);
lean_closure_set(v___f_1061_, 0, v_target_1047_);
lean_closure_set(v___f_1061_, 1, v_kind_1055_);
lean_closure_set(v___f_1061_, 2, v_facet_1048_);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
v___x_1064_ = l_Lake_Job_bindM___redArg(v_outKind_1060_, v_a_1050_, v___f_1061_, v___x_1062_, v___x_1056_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v___x_1063_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1064_);
v___x_1066_ = v___x_1053_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_a_1051_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_dec(v___x_1058_);
lean_dec(v_a_1050_);
lean_dec_ref(v_target_1047_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
v___x_1068_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1069_ = l_Lake_BuildKey_toString(v_root_891_);
v___x_1070_ = lean_string_append(v___x_1068_, v___x_1069_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
v___x_1072_ = lean_string_append(v___x_1070_, v___x_1071_);
v___x_1073_ = 1;
v___x_1074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_1048_, v___x_1073_);
v___x_1075_ = lean_string_append(v___x_1072_, v___x_1074_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
v___x_1078_ = 3;
v___x_1079_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*1, v___x_1078_);
v___x_1080_ = lean_array_get_size(v_a_1051_);
v___x_1081_ = lean_array_push(v_a_1051_, v___x_1079_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 1, v___x_1081_);
lean_ctor_set(v___x_1053_, 0, v___x_1080_);
v___x_1083_ = v___x_1053_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_a_1050_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec_ref(v_root_891_);
v___x_1085_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
v___x_1086_ = l_Lake_BuildKey_toString(v_self_892_);
v___x_1087_ = lean_string_append(v___x_1085_, v___x_1086_);
lean_dec_ref(v___x_1086_);
v___x_1088_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
v___x_1089_ = lean_string_append(v___x_1087_, v___x_1088_);
v___x_1090_ = 3;
v___x_1091_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*1, v___x_1090_);
v___x_1092_ = lean_array_get_size(v_a_1051_);
v___x_1093_ = lean_array_push(v_a_1051_, v___x_1091_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 1, v___x_1093_);
lean_ctor_set(v___x_1053_, 0, v___x_1092_);
v___x_1095_ = v___x_1053_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_dec_ref(v_self_892_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec_ref(v_root_891_);
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___boxed(lean_object* v_root_1098_, lean_object* v_self_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_root_1098_, v_self_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg(lean_object* v_self_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; 
lean_inc_ref(v_self_1108_);
v___x_1116_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_self_1108_, v_self_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg___boxed(lean_object* v_self_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lake_BuildKey_fetch___redArg(v_self_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object* v_00_u03b1_1126_, lean_object* v_self_1127_, lean_object* v_inst_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; 
lean_inc_ref(v_self_1127_);
v___x_1136_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(v_self_1127_, v_self_1127_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___boxed(lean_object* v_00_u03b1_1137_, lean_object* v_self_1138_, lean_object* v_inst_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lake_BuildKey_fetch(v_00_u03b1_1137_, v_self_1138_, v_inst_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg(lean_object* v_inst_1152_, lean_object* v_defaultPkg_1153_, lean_object* v_self_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
uint8_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = 1;
lean_inc_ref_n(v_self_1154_, 2);
v___x_1163_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1153_, v_self_1154_, v_self_1154_, v___x_1162_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1205_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_a_1165_ = lean_ctor_get(v___x_1163_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1167_ = v___x_1163_;
v_isShared_1168_ = v_isSharedCheck_1205_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1205_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___y_1170_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1203_; 
v_snd_1188_ = lean_ctor_get(v_a_1164_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1164_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_a_1164_, 0);
lean_dec(v_unused_1204_);
v___x_1190_ = v_a_1164_;
v_isShared_1191_ = v_isSharedCheck_1203_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_dec(v_a_1164_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1203_;
goto v_resetjp_1189_;
}
v___jp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1171_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__0));
v___x_1172_ = l_Lake_PartialBuildKey_toString(v_self_1154_);
v___x_1173_ = lean_string_append(v___x_1171_, v___x_1172_);
lean_dec_ref(v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__1));
v___x_1175_ = lean_string_append(v___x_1173_, v___x_1174_);
v___x_1176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_1152_, v___x_1162_);
v___x_1177_ = lean_string_append(v___x_1175_, v___x_1176_);
lean_dec_ref(v___x_1176_);
v___x_1178_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__2));
v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
v___x_1180_ = lean_string_append(v___x_1179_, v___y_1170_);
lean_dec_ref(v___y_1170_);
v___x_1181_ = 3;
v___x_1182_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*1, v___x_1181_);
v___x_1183_ = lean_array_get_size(v_a_1165_);
v___x_1184_ = lean_array_push(v_a_1165_, v___x_1182_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 1);
lean_ctor_set(v___x_1167_, 1, v___x_1184_);
lean_ctor_set(v___x_1167_, 0, v___x_1183_);
v___x_1186_ = v___x_1167_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
v_resetjp_1189_:
{
lean_object* v_kind_1192_; uint8_t v___x_1193_; 
v_kind_1192_ = lean_ctor_get(v_snd_1188_, 1);
v___x_1193_ = lean_name_eq(v_kind_1192_, v_inst_1152_);
if (v___x_1193_ == 0)
{
uint8_t v___x_1194_; 
lean_inc(v_kind_1192_);
lean_del_object(v___x_1190_);
lean_dec(v_snd_1188_);
v___x_1194_ = l_Lean_Name_isAnonymous(v_kind_1192_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
v___x_1196_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1192_, v___x_1162_);
v___x_1197_ = lean_string_append(v___x_1195_, v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = lean_string_append(v___x_1197_, v___x_1195_);
v___y_1170_ = v___x_1198_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1199_; 
lean_dec(v_kind_1192_);
v___x_1199_ = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__3));
v___y_1170_ = v___x_1199_;
goto v___jp_1169_;
}
}
else
{
lean_object* v___x_1201_; 
lean_del_object(v___x_1167_);
lean_dec_ref(v_self_1154_);
lean_dec(v_inst_1152_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_a_1165_);
lean_ctor_set(v___x_1190_, 0, v_snd_1188_);
v___x_1201_ = v___x_1190_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_snd_1188_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_a_1165_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v_self_1154_);
lean_dec(v_inst_1152_);
v_a_1206_ = lean_ctor_get(v___x_1163_, 0);
v_a_1207_ = lean_ctor_get(v___x_1163_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1163_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_inc(v_a_1206_);
lean_dec(v___x_1163_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1206_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg___boxed(lean_object* v_inst_1215_, lean_object* v_defaultPkg_1216_, lean_object* v_self_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lake_Target_fetchIn___redArg(v_inst_1215_, v_defaultPkg_1216_, v_self_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn(lean_object* v_00_u03b1_1226_, lean_object* v_inst_1227_, lean_object* v_defaultPkg_1228_, lean_object* v_self_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lake_Target_fetchIn___redArg(v_inst_1227_, v_defaultPkg_1228_, v_self_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_inst_1239_, lean_object* v_defaultPkg_1240_, lean_object* v_self_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lake_Target_fetchIn(v_00_u03b1_1238_, v_inst_1239_, v_defaultPkg_1240_, v_self_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0(lean_object* v_inst_1250_, lean_object* v_defaultPkg_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lake_Target_fetchIn___redArg(v_inst_1250_, v_defaultPkg_1251_, v_x_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed(lean_object* v_inst_1261_, lean_object* v_defaultPkg_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lake_TargetArray_fetchIn___redArg___lam__0(v_inst_1261_, v_defaultPkg_1262_, v_x_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v_res_1271_;
}
}
static lean_object* _init_l_Lake_TargetArray_fetchIn___redArg___closed__0(void){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_instMonadST(lean_box(0));
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object* v_inst_1273_, lean_object* v_defaultPkg_1274_, lean_object* v_self_1275_, lean_object* v_traceCaption_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; lean_object* v_toApplicative_1285_; lean_object* v_toBind_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1340_; 
v___x_1284_ = lean_obj_once(&l_Lake_TargetArray_fetchIn___redArg___closed__0, &l_Lake_TargetArray_fetchIn___redArg___closed__0_once, _init_l_Lake_TargetArray_fetchIn___redArg___closed__0);
v_toApplicative_1285_ = lean_ctor_get(v___x_1284_, 0);
v_toBind_1286_ = lean_ctor_get(v___x_1284_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1288_ = v___x_1284_;
v_isShared_1289_ = v_isSharedCheck_1340_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_toBind_1286_);
lean_inc(v_toApplicative_1285_);
lean_dec(v___x_1284_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1340_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_toFunctor_1290_; lean_object* v_toPure_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1336_; 
v_toFunctor_1290_ = lean_ctor_get(v_toApplicative_1285_, 0);
v_toPure_1291_ = lean_ctor_get(v_toApplicative_1285_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_toApplicative_1285_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1337_ = lean_ctor_get(v_toApplicative_1285_, 4);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_toApplicative_1285_, 3);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_toApplicative_1285_, 2);
lean_dec(v_unused_1339_);
v___x_1293_ = v_toApplicative_1285_;
v_isShared_1294_ = v_isSharedCheck_1336_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_toPure_1291_);
lean_inc(v_toFunctor_1290_);
lean_dec(v_toApplicative_1285_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1336_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___f_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; lean_object* v___x_1303_; 
v___f_1295_ = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_1295_, 0, v_inst_1273_);
lean_closure_set(v___f_1295_, 1, v_defaultPkg_1274_);
lean_inc(v_toBind_1286_);
lean_inc(v_toPure_1291_);
v___f_1296_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1296_, 0, v_toPure_1291_);
lean_closure_set(v___f_1296_, 1, v_toBind_1286_);
lean_inc(v_toBind_1286_);
lean_inc(v_toPure_1291_);
v___f_1297_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1297_, 0, v_toPure_1291_);
lean_closure_set(v___f_1297_, 1, v_toBind_1286_);
lean_inc_ref(v___f_1296_);
lean_inc(v_toPure_1291_);
v___f_1298_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1298_, 0, v_toPure_1291_);
lean_closure_set(v___f_1298_, 1, v___f_1296_);
lean_inc(v_toPure_1291_);
lean_inc_ref(v_toFunctor_1290_);
v___f_1299_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1299_, 0, v_toFunctor_1290_);
lean_closure_set(v___f_1299_, 1, v_toPure_1291_);
lean_closure_set(v___f_1299_, 2, v_toBind_1286_);
v___x_1300_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1290_);
v___f_1301_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1301_, 0, v_toPure_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___f_1297_);
lean_ctor_set(v___x_1293_, 3, v___f_1298_);
lean_ctor_set(v___x_1293_, 2, v___f_1299_);
lean_ctor_set(v___x_1293_, 1, v___f_1301_);
lean_ctor_set(v___x_1293_, 0, v___x_1300_);
v___x_1303_ = v___x_1293_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___f_1301_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v___f_1299_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___f_1298_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v___f_1297_);
v___x_1303_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___f_1296_);
lean_ctor_set(v___x_1288_, 0, v___x_1303_);
v___x_1305_ = v___x_1288_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___f_1296_);
v___x_1305_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_691__overap_1313_; lean_object* v___x_1314_; 
v___x_1306_ = l_ReaderT_instMonad___redArg(v___x_1305_);
v___x_1307_ = l_ReaderT_instMonad___redArg(v___x_1306_);
v___x_1308_ = l_ReaderT_instMonad___redArg(v___x_1307_);
v___x_1309_ = l_ReaderT_instMonad___redArg(v___x_1308_);
v___x_1310_ = l_Lake_EquipT_instMonad___redArg(v___x_1309_);
v_sz_1311_ = lean_array_size(v_self_1275_);
v___x_1312_ = ((size_t)0ULL);
v___x_691__overap_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1310_, v___f_1295_, v_sz_1311_, v___x_1312_, v_self_1275_);
v___x_1314_ = lean_apply_7(v___x_691__overap_1313_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, lean_box(0));
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_a_1316_ = lean_ctor_get(v___x_1314_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1314_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = l_Lake_Job_collectArray___redArg(v_a_1315_, v_traceCaption_1276_);
lean_dec(v_a_1315_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_a_1316_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_traceCaption_1276_);
v_a_1325_ = lean_ctor_get(v___x_1314_, 0);
v_a_1326_ = lean_ctor_get(v___x_1314_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1314_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_inc(v_a_1325_);
lean_dec(v___x_1314_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1325_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___boxed(lean_object* v_inst_1341_, lean_object* v_defaultPkg_1342_, lean_object* v_self_1343_, lean_object* v_traceCaption_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lake_TargetArray_fetchIn___redArg(v_inst_1341_, v_defaultPkg_1342_, v_self_1343_, v_traceCaption_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn(lean_object* v_00_u03b1_1353_, lean_object* v_inst_1354_, lean_object* v_defaultPkg_1355_, lean_object* v_self_1356_, lean_object* v_traceCaption_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lake_TargetArray_fetchIn___redArg(v_inst_1354_, v_defaultPkg_1355_, v_self_1356_, v_traceCaption_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_inst_1367_, lean_object* v_defaultPkg_1368_, lean_object* v_self_1369_, lean_object* v_traceCaption_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lake_TargetArray_fetchIn(v_00_u03b1_1366_, v_inst_1367_, v_defaultPkg_1368_, v_self_1369_, v_traceCaption_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
return v_res_1378_;
}
}
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Key(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
