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
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invalid target '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "': package '"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "' not found in workspace"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value;
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value),LEAN_SCALAR_PTR_LITERAL(29, 214, 131, 210, 10, 90, 37, 134)}};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "': targets of opaque data kinds do not support facets"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value;
extern lean_object* l_Lake_instDataKindModule;
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
extern lean_object* l_Lake_instDataKindPackage;
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
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
lean_object* l_instMonadST(lean_object*);
static lean_once_cell_t l_Lake_TargetArray_fetchIn___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_TargetArray_fetchIn___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_25; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_dec_ref(x_4);
x_27 = lean_ctor_get(x_26, 6);
lean_inc(x_27);
lean_dec(x_26);
x_28 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(x_3);
x_29 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_28, x_27, x_3);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_29);
x_32 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_33 = l_Lake_PartialBuildKey_toString(x_2);
x_34 = lean_string_append(x_32, x_33);
lean_dec_ref(x_33);
x_35 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_36 = lean_string_append(x_34, x_35);
x_37 = 1;
x_38 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_37);
x_39 = lean_string_append(x_36, x_38);
lean_dec_ref(x_38);
x_40 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_41 = lean_string_append(x_39, x_40);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_get_size(x_5);
x_45 = lean_array_push(x_5, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_65; 
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_dec_ref(x_4);
x_48 = lean_ctor_get(x_47, 5);
lean_inc_ref(x_48);
lean_dec(x_47);
x_49 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13));
x_50 = lean_box(0);
x_51 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
lean_inc(x_3);
x_52 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_52, 0, x_3);
lean_closure_set(x_52, 1, x_51);
lean_closure_set(x_52, 2, x_50);
x_53 = lean_array_size(x_48);
x_54 = 0;
x_55 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_49, x_48, x_52, x_53, x_54, x_51);
x_56 = lean_ctor_get(x_55, 0);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_55, 1);
lean_dec(x_66);
x_57 = x_55;
x_58 = x_65;
goto block_64;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_65;
goto block_64;
}
block_64:
{
if (lean_obj_tag(x_56) == 0)
{
lean_del_object(x_57);
x_7 = x_5;
x_8 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec_ref(x_56);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
if (x_58 == 0)
{
lean_ctor_set(x_57, 1, x_5);
lean_ctor_set(x_57, 0, x_60);
x_61 = x_57;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_5);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
else
{
lean_dec(x_59);
lean_del_object(x_57);
x_7 = x_5;
x_8 = lean_box(0);
goto block_24;
}
}
}
}
}
block_24:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_10 = l_Lake_PartialBuildKey_toString(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = 1;
x_15 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_18 = lean_string_append(x_16, x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_7);
x_22 = lean_array_push(x_7, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_29; 
lean_dec_ref(x_8);
lean_dec_ref(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec_ref(x_8);
x_31 = lean_ctor_get(x_30, 6);
lean_inc(x_31);
lean_dec(x_30);
x_32 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(x_3);
x_33 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_32, x_31, x_3);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_33);
x_36 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_37 = l_Lake_PartialBuildKey_toString(x_2);
x_38 = lean_string_append(x_36, x_37);
lean_dec_ref(x_37);
x_39 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_40 = lean_string_append(x_38, x_39);
x_41 = 1;
x_42 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_41);
x_43 = lean_string_append(x_40, x_42);
lean_dec_ref(x_42);
x_44 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_45 = lean_string_append(x_43, x_44);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_get_size(x_9);
x_49 = lean_array_push(x_9, x_47);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_69; 
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_dec_ref(x_8);
x_52 = lean_ctor_get(x_51, 5);
lean_inc_ref(x_52);
lean_dec(x_51);
x_53 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13));
x_54 = lean_box(0);
x_55 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
lean_inc(x_3);
x_56 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_56, 0, x_3);
lean_closure_set(x_56, 1, x_55);
lean_closure_set(x_56, 2, x_54);
x_57 = lean_array_size(x_52);
x_58 = 0;
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_53, x_52, x_56, x_57, x_58, x_55);
x_60 = lean_ctor_get(x_59, 0);
x_69 = !lean_is_exclusive(x_59);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_59, 1);
lean_dec(x_70);
x_61 = x_59;
x_62 = x_69;
goto block_68;
}
else
{
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = x_69;
goto block_68;
}
block_68:
{
if (lean_obj_tag(x_60) == 0)
{
lean_del_object(x_61);
x_11 = x_9;
x_12 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec_ref(x_60);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
if (x_62 == 0)
{
lean_ctor_set(x_61, 1, x_9);
lean_ctor_set(x_61, 0, x_64);
x_65 = x_61;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_9);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
else
{
lean_dec(x_63);
lean_del_object(x_61);
x_11 = x_9;
x_12 = lean_box(0);
goto block_28;
}
}
}
}
}
block_28:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_14 = l_Lake_PartialBuildKey_toString(x_2);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_17 = lean_string_append(x_15, x_16);
x_18 = 1;
x_19 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_22 = lean_string_append(x_20, x_21);
x_23 = 3;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_array_get_size(x_11);
x_26 = lean_array_push(x_11, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_46; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
x_17 = x_10;
x_18 = x_46;
goto block_45;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_3);
x_20 = lean_apply_7(x_5, x_19, x_6, x_7, x_8, x_9, x_12, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_32; 
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
x_23 = x_20;
x_24 = x_32;
goto block_31;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_25; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_22);
x_25 = x_17;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_16);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_14);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_44; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
x_35 = x_20;
x_36 = x_44;
goto block_43;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_box(0);
x_36 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_37; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_34);
x_37 = x_17;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_15);
lean_ctor_set(x_42, 2, x_16);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_42, sizeof(void*)*3 + 1, x_14);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_5);
x_7 = lean_array_uget_borrowed(x_2, x_4);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_box(0);
x_10 = lean_name_eq(x_8, x_1);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2));
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
x_3 = 0;
x_4 = 0;
x_5 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0));
x_6 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_27; 
x_27 = l_Lake_instDataKindModule;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec_ref(x_3);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_dec_ref(x_9);
lean_inc(x_28);
x_30 = l_Lake_Workspace_findModule_x3f(x_28, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_32, 0);
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
x_36 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_37 = 0;
x_38 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_task_pure(x_39);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_30);
x_44 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_45 = l_Lake_PartialBuildKey_toString(x_2);
x_46 = lean_string_append(x_44, x_45);
lean_dec_ref(x_45);
x_47 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
x_48 = lean_string_append(x_46, x_47);
x_49 = 1;
x_50 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_28, x_49);
x_51 = lean_string_append(x_48, x_50);
lean_dec_ref(x_50);
x_52 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_53 = lean_string_append(x_51, x_52);
x_54 = 3;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_get_size(x_10);
x_57 = lean_array_push(x_10, x_55);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
case 1:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_124; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_59 = lean_ctor_get(x_3, 0);
x_124 = !lean_is_exclusive(x_3);
if (x_124 == 0)
{
x_60 = x_3;
x_61 = x_124;
goto block_123;
}
else
{
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_box(0);
x_61 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_62; lean_object* x_63; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = l_Lake_instDataKindPackage;
switch (lean_obj_tag(x_59)) {
case 0:
{
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_80 = x_1;
x_81 = x_10;
x_82 = lean_box(0);
goto block_95;
}
case 2:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_1);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
lean_dec_ref(x_9);
x_97 = lean_ctor_get(x_96, 6);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_97, x_59);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_99; 
lean_dec_ref(x_59);
lean_dec_ref(x_2);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_80 = x_99;
x_81 = x_10;
x_82 = lean_box(0);
goto block_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_98);
lean_del_object(x_60);
x_100 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_101 = l_Lake_PartialBuildKey_toString(x_2);
x_102 = lean_string_append(x_100, x_101);
lean_dec_ref(x_101);
x_103 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_104 = lean_string_append(x_102, x_103);
x_105 = 1;
x_106 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_59, x_105);
x_107 = lean_string_append(x_104, x_106);
lean_dec_ref(x_106);
x_108 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_109 = lean_string_append(x_107, x_108);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_get_size(x_10);
x_113 = lean_array_push(x_10, x_111);
x_22 = x_112;
x_23 = x_113;
x_24 = lean_box(0);
goto block_26;
}
}
default: 
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_9, 1);
lean_inc(x_114);
lean_dec_ref(x_9);
x_115 = lean_ctor_get(x_114, 5);
lean_inc_ref(x_115);
lean_dec(x_114);
x_116 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_117 = lean_array_size(x_115);
x_118 = 0;
x_119 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_59, x_115, x_117, x_118, x_116);
lean_dec_ref(x_115);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_del_object(x_60);
x_62 = x_10;
x_63 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
if (lean_obj_tag(x_121) == 1)
{
lean_object* x_122; 
lean_dec(x_59);
lean_dec_ref(x_2);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_80 = x_122;
x_81 = x_10;
x_82 = lean_box(0);
goto block_95;
}
else
{
lean_dec(x_121);
lean_del_object(x_60);
x_62 = x_10;
x_63 = lean_box(0);
goto block_78;
}
}
}
}
block_78:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_65 = l_Lake_PartialBuildKey_toString(x_2);
x_66 = lean_string_append(x_64, x_65);
lean_dec_ref(x_65);
x_67 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_68 = lean_string_append(x_66, x_67);
x_69 = 1;
x_70 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_59, x_69);
x_71 = lean_string_append(x_68, x_70);
lean_dec_ref(x_70);
x_72 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_73 = lean_string_append(x_71, x_72);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_get_size(x_62);
x_77 = lean_array_push(x_62, x_75);
x_22 = x_76;
x_23 = x_77;
x_24 = lean_box(0);
goto block_26;
}
block_95:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 2);
lean_inc(x_83);
if (x_61 == 0)
{
lean_ctor_set(x_60, 0, x_83);
x_84 = x_60;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_83);
x_84 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_86 = 0;
x_87 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_task_pure(x_88);
x_90 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_79);
lean_ctor_set(x_90, 2, x_85);
lean_ctor_set_uint8(x_90, sizeof(void*)*3, x_86);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_81);
return x_92;
}
}
}
}
case 2:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_213; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_125 = lean_ctor_get(x_3, 0);
x_126 = lean_ctor_get(x_3, 1);
x_213 = !lean_is_exclusive(x_3);
if (x_213 == 0)
{
x_127 = x_3;
x_128 = x_213;
goto block_212;
}
else
{
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_3);
x_127 = lean_box(0);
x_128 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_168; lean_object* x_169; 
switch (lean_obj_tag(x_125)) {
case 0:
{
lean_dec_ref(x_9);
x_129 = x_1;
x_130 = x_10;
x_131 = lean_box(0);
goto block_167;
}
case 2:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_9, 1);
lean_inc(x_185);
lean_dec_ref(x_9);
x_186 = lean_ctor_get(x_185, 6);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_186, x_125);
lean_dec(x_186);
if (lean_obj_tag(x_187) == 1)
{
lean_object* x_188; 
lean_dec_ref(x_125);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_129 = x_188;
x_130 = x_10;
x_131 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_187);
lean_del_object(x_127);
lean_dec(x_126);
x_189 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_190 = l_Lake_PartialBuildKey_toString(x_2);
x_191 = lean_string_append(x_189, x_190);
lean_dec_ref(x_190);
x_192 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_193 = lean_string_append(x_191, x_192);
x_194 = 1;
x_195 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_125, x_194);
x_196 = lean_string_append(x_193, x_195);
lean_dec_ref(x_195);
x_197 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_198 = lean_string_append(x_196, x_197);
x_199 = 3;
x_200 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_199);
x_201 = lean_array_get_size(x_10);
x_202 = lean_array_push(x_10, x_200);
x_17 = x_201;
x_18 = x_202;
x_19 = lean_box(0);
goto block_21;
}
}
default: 
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; size_t x_206; size_t x_207; lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_1);
x_203 = lean_ctor_get(x_9, 1);
lean_inc(x_203);
lean_dec_ref(x_9);
x_204 = lean_ctor_get(x_203, 5);
lean_inc_ref(x_204);
lean_dec(x_203);
x_205 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_206 = lean_array_size(x_204);
x_207 = 0;
x_208 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_125, x_204, x_206, x_207, x_205);
lean_dec_ref(x_204);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_del_object(x_127);
lean_dec(x_126);
x_168 = x_10;
x_169 = lean_box(0);
goto block_184;
}
else
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
if (lean_obj_tag(x_210) == 1)
{
lean_object* x_211; 
lean_dec(x_125);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_129 = x_211;
x_130 = x_10;
x_131 = lean_box(0);
goto block_167;
}
else
{
lean_dec(x_210);
lean_del_object(x_127);
lean_dec(x_126);
x_168 = x_10;
x_169 = lean_box(0);
goto block_184;
}
}
}
}
block_167:
{
lean_object* x_132; 
lean_inc_ref(x_129);
lean_inc(x_126);
x_132 = l_Lake_Package_findTargetModule_x3f(x_126, x_129);
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_2);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_ctor_get(x_129, 2);
lean_inc(x_134);
lean_dec_ref(x_129);
if (x_128 == 0)
{
lean_ctor_set(x_127, 0, x_134);
x_135 = x_127;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_134);
lean_ctor_set(x_145, 1, x_126);
x_135 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_137 = 0;
x_138 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_task_pure(x_139);
x_141 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_27);
lean_ctor_set(x_141, 2, x_136);
lean_ctor_set_uint8(x_141, sizeof(void*)*3, x_137);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_135);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_130);
return x_143;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_132);
lean_del_object(x_127);
x_146 = lean_ctor_get(x_129, 1);
lean_inc(x_146);
lean_dec_ref(x_129);
x_147 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_148 = l_Lake_PartialBuildKey_toString(x_2);
x_149 = lean_string_append(x_147, x_148);
lean_dec_ref(x_148);
x_150 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6));
x_151 = lean_string_append(x_149, x_150);
x_152 = 1;
x_153 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_126, x_152);
x_154 = lean_string_append(x_151, x_153);
lean_dec_ref(x_153);
x_155 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
x_156 = lean_string_append(x_154, x_155);
x_157 = 0;
x_158 = l_Lean_Name_toString(x_146, x_157);
x_159 = lean_string_append(x_156, x_158);
lean_dec_ref(x_158);
x_160 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_161 = lean_string_append(x_159, x_160);
x_162 = 3;
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_array_get_size(x_130);
x_165 = lean_array_push(x_130, x_163);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
block_184:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_170 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_171 = l_Lake_PartialBuildKey_toString(x_2);
x_172 = lean_string_append(x_170, x_171);
lean_dec_ref(x_171);
x_173 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_174 = lean_string_append(x_172, x_173);
x_175 = 1;
x_176 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_125, x_175);
x_177 = lean_string_append(x_174, x_176);
lean_dec_ref(x_176);
x_178 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_179 = lean_string_append(x_177, x_178);
x_180 = 3;
x_181 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*1, x_180);
x_182 = lean_array_get_size(x_168);
x_183 = lean_array_push(x_168, x_181);
x_17 = x_182;
x_18 = x_183;
x_19 = lean_box(0);
goto block_21;
}
}
}
case 3:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_367; 
x_214 = lean_ctor_get(x_3, 0);
x_215 = lean_ctor_get(x_3, 1);
x_367 = !lean_is_exclusive(x_3);
if (x_367 == 0)
{
x_216 = x_3;
x_217 = x_367;
goto block_366;
}
else
{
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_3);
x_216 = lean_box(0);
x_217 = x_367;
goto block_366;
}
block_366:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_322; lean_object* x_323; 
switch (lean_obj_tag(x_214)) {
case 0:
{
x_218 = x_1;
x_219 = x_10;
x_220 = lean_box(0);
goto block_321;
}
case 2:
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec_ref(x_1);
x_339 = lean_ctor_get(x_9, 1);
x_340 = lean_ctor_get(x_339, 6);
x_341 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_340, x_214);
if (lean_obj_tag(x_341) == 1)
{
lean_object* x_342; 
lean_dec_ref(x_214);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec_ref(x_341);
x_218 = x_342;
x_219 = x_10;
x_220 = lean_box(0);
goto block_321;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_341);
lean_del_object(x_216);
lean_dec(x_215);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_343 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_344 = l_Lake_PartialBuildKey_toString(x_2);
x_345 = lean_string_append(x_343, x_344);
lean_dec_ref(x_344);
x_346 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_347 = lean_string_append(x_345, x_346);
x_348 = 1;
x_349 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_214, x_348);
x_350 = lean_string_append(x_347, x_349);
lean_dec_ref(x_349);
x_351 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_352 = lean_string_append(x_350, x_351);
x_353 = 3;
x_354 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_353);
x_355 = lean_array_get_size(x_10);
x_356 = lean_array_push(x_10, x_354);
x_12 = x_355;
x_13 = x_356;
x_14 = lean_box(0);
goto block_16;
}
}
default: 
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; size_t x_360; size_t x_361; lean_object* x_362; lean_object* x_363; 
lean_dec_ref(x_1);
x_357 = lean_ctor_get(x_9, 1);
x_358 = lean_ctor_get(x_357, 5);
x_359 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_360 = lean_array_size(x_358);
x_361 = 0;
x_362 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_214, x_358, x_360, x_361, x_359);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
if (lean_obj_tag(x_363) == 0)
{
lean_del_object(x_216);
lean_dec(x_215);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_322 = x_10;
x_323 = lean_box(0);
goto block_338;
}
else
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
lean_dec_ref(x_363);
if (lean_obj_tag(x_364) == 1)
{
lean_object* x_365; 
lean_dec(x_214);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_218 = x_365;
x_219 = x_10;
x_220 = lean_box(0);
goto block_321;
}
else
{
lean_dec(x_364);
lean_del_object(x_216);
lean_dec(x_215);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_322 = x_10;
x_323 = lean_box(0);
goto block_338;
}
}
}
}
block_321:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_218, 1);
x_222 = lean_ctor_get(x_218, 2);
lean_inc(x_215);
lean_inc(x_222);
if (x_217 == 0)
{
lean_ctor_set(x_216, 0, x_222);
x_223 = x_216;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_320, 0, x_222);
lean_ctor_set(x_320, 1, x_215);
x_223 = x_320;
goto block_319;
}
block_319:
{
if (x_4 == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec_ref(x_2);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_218);
lean_ctor_set(x_224, 1, x_215);
x_225 = lean_apply_7(x_5, x_224, x_6, x_7, x_8, x_9, x_219, lean_box(0));
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_235; 
x_226 = lean_ctor_get(x_225, 0);
x_227 = lean_ctor_get(x_225, 1);
x_235 = !lean_is_exclusive(x_225);
if (x_235 == 0)
{
x_228 = x_225;
x_229 = x_235;
goto block_234;
}
else
{
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_225);
x_228 = lean_box(0);
x_229 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_226);
if (x_229 == 0)
{
lean_ctor_set(x_228, 0, x_230);
x_231 = x_228;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_227);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_244; 
lean_dec_ref(x_223);
x_236 = lean_ctor_get(x_225, 0);
x_237 = lean_ctor_get(x_225, 1);
x_244 = !lean_is_exclusive(x_225);
if (x_244 == 0)
{
x_238 = x_225;
x_239 = x_244;
goto block_243;
}
else
{
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_225);
x_238 = lean_box(0);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
if (x_239 == 0)
{
x_240 = x_238;
goto block_241;
}
else
{
lean_object* x_242; 
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_237);
x_240 = x_242;
goto block_241;
}
block_241:
{
return x_240;
}
}
}
}
else
{
lean_object* x_245; 
x_245 = l_Lake_Package_findTargetDecl_x3f(x_215, x_218);
if (lean_obj_tag(x_245) == 1)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_302; 
lean_dec_ref(x_2);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = lean_ctor_get(x_246, 1);
x_248 = lean_ctor_get(x_246, 2);
x_249 = lean_ctor_get(x_246, 3);
x_302 = !lean_is_exclusive(x_246);
if (x_302 == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_246, 0);
lean_dec(x_303);
x_250 = x_246;
x_251 = x_302;
goto block_301;
}
else
{
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_246);
x_250 = lean_box(0);
x_251 = x_302;
goto block_301;
}
block_301:
{
uint8_t x_252; 
x_252 = l_Lean_Name_isAnonymous(x_248);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_215);
x_253 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9));
lean_inc(x_248);
x_254 = l_Lean_Name_str___override(x_248, x_253);
x_255 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_255, 0, x_218);
lean_ctor_set(x_255, 1, x_247);
lean_ctor_set(x_255, 2, x_249);
lean_inc(x_254);
lean_inc_ref(x_223);
if (x_251 == 0)
{
lean_ctor_set_tag(x_250, 1);
lean_ctor_set(x_250, 3, x_254);
lean_ctor_set(x_250, 2, x_255);
lean_ctor_set(x_250, 1, x_248);
lean_ctor_set(x_250, 0, x_223);
x_256 = x_250;
goto block_278;
}
else
{
lean_object* x_279; 
x_279 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_279, 0, x_223);
lean_ctor_set(x_279, 1, x_248);
lean_ctor_set(x_279, 2, x_255);
lean_ctor_set(x_279, 3, x_254);
x_256 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_257; 
x_257 = lean_apply_7(x_5, x_256, x_6, x_7, x_8, x_9, x_219, lean_box(0));
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_268; 
x_258 = lean_ctor_get(x_257, 0);
x_259 = lean_ctor_get(x_257, 1);
x_268 = !lean_is_exclusive(x_257);
if (x_268 == 0)
{
x_260 = x_257;
x_261 = x_268;
goto block_267;
}
else
{
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_257);
x_260 = lean_box(0);
x_261 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_262, 0, x_223);
lean_ctor_set(x_262, 1, x_254);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_258);
if (x_261 == 0)
{
lean_ctor_set(x_260, 0, x_263);
x_264 = x_260;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_259);
x_264 = x_266;
goto block_265;
}
block_265:
{
return x_264;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_277; 
lean_dec(x_254);
lean_dec_ref(x_223);
x_269 = lean_ctor_get(x_257, 0);
x_270 = lean_ctor_get(x_257, 1);
x_277 = !lean_is_exclusive(x_257);
if (x_277 == 0)
{
x_271 = x_257;
x_272 = x_277;
goto block_276;
}
else
{
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_257);
x_271 = lean_box(0);
x_272 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_273; 
if (x_272 == 0)
{
x_273 = x_271;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_270);
x_273 = x_275;
goto block_274;
}
block_274:
{
return x_273;
}
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_del_object(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_218);
lean_ctor_set(x_280, 1, x_215);
x_281 = lean_apply_7(x_5, x_280, x_6, x_7, x_8, x_9, x_219, lean_box(0));
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_291; 
x_282 = lean_ctor_get(x_281, 0);
x_283 = lean_ctor_get(x_281, 1);
x_291 = !lean_is_exclusive(x_281);
if (x_291 == 0)
{
x_284 = x_281;
x_285 = x_291;
goto block_290;
}
else
{
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_281);
x_284 = lean_box(0);
x_285 = x_291;
goto block_290;
}
block_290:
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_223);
lean_ctor_set(x_286, 1, x_282);
if (x_285 == 0)
{
lean_ctor_set(x_284, 0, x_286);
x_287 = x_284;
goto block_288;
}
else
{
lean_object* x_289; 
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_283);
x_287 = x_289;
goto block_288;
}
block_288:
{
return x_287;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_300; 
lean_dec_ref(x_223);
x_292 = lean_ctor_get(x_281, 0);
x_293 = lean_ctor_get(x_281, 1);
x_300 = !lean_is_exclusive(x_281);
if (x_300 == 0)
{
x_294 = x_281;
x_295 = x_300;
goto block_299;
}
else
{
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_281);
x_294 = lean_box(0);
x_295 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_296; 
if (x_295 == 0)
{
x_296 = x_294;
goto block_297;
}
else
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_292);
lean_ctor_set(x_298, 1, x_293);
x_296 = x_298;
goto block_297;
}
block_297:
{
return x_296;
}
}
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_inc(x_221);
lean_dec(x_245);
lean_dec_ref(x_223);
lean_dec_ref(x_218);
lean_dec(x_215);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_304 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_305 = l_Lake_PartialBuildKey_toString(x_2);
x_306 = lean_string_append(x_304, x_305);
lean_dec_ref(x_305);
x_307 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10));
x_308 = lean_string_append(x_306, x_307);
x_309 = 0;
x_310 = l_Lean_Name_toString(x_221, x_309);
x_311 = lean_string_append(x_308, x_310);
lean_dec_ref(x_310);
x_312 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_313 = lean_string_append(x_311, x_312);
x_314 = 3;
x_315 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set_uint8(x_315, sizeof(void*)*1, x_314);
x_316 = lean_array_get_size(x_219);
x_317 = lean_array_push(x_219, x_315);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
}
block_338:
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_324 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_325 = l_Lake_PartialBuildKey_toString(x_2);
x_326 = lean_string_append(x_324, x_325);
lean_dec_ref(x_325);
x_327 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_328 = lean_string_append(x_326, x_327);
x_329 = 1;
x_330 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_214, x_329);
x_331 = lean_string_append(x_328, x_330);
lean_dec_ref(x_330);
x_332 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_333 = lean_string_append(x_331, x_332);
x_334 = 3;
x_335 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set_uint8(x_335, sizeof(void*)*1, x_334);
x_336 = lean_array_get_size(x_322);
x_337 = lean_array_push(x_322, x_335);
x_12 = x_336;
x_13 = x_337;
x_14 = lean_box(0);
goto block_16;
}
}
}
default: 
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; uint8_t x_439; 
x_368 = lean_ctor_get(x_3, 0);
x_369 = lean_ctor_get(x_3, 1);
x_439 = !lean_is_exclusive(x_3);
if (x_439 == 0)
{
x_370 = x_3;
x_371 = x_439;
goto block_438;
}
else
{
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_3);
x_370 = lean_box(0);
x_371 = x_439;
goto block_438;
}
block_438:
{
uint8_t x_372; lean_object* x_373; 
x_372 = 0;
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_368);
lean_inc_ref(x_2);
x_373 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_368, x_372, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; uint8_t x_436; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_374, 1);
x_436 = !lean_is_exclusive(x_374);
if (x_436 == 0)
{
lean_object* x_437; 
x_437 = lean_ctor_get(x_374, 0);
lean_dec(x_437);
x_376 = x_374;
x_377 = x_436;
goto block_435;
}
else
{
lean_inc(x_375);
lean_dec(x_374);
x_376 = lean_box(0);
x_377 = x_436;
goto block_435;
}
block_435:
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; uint8_t x_433; 
x_378 = lean_ctor_get(x_373, 1);
x_433 = !lean_is_exclusive(x_373);
if (x_433 == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_373, 0);
lean_dec(x_434);
x_379 = x_373;
x_380 = x_433;
goto block_432;
}
else
{
lean_inc(x_378);
lean_dec(x_373);
x_379 = lean_box(0);
x_380 = x_433;
goto block_432;
}
block_432:
{
lean_object* x_381; lean_object* x_382; uint8_t x_419; 
x_381 = lean_ctor_get(x_375, 1);
x_419 = l_Lean_Name_isAnonymous(x_381);
if (x_419 == 0)
{
uint8_t x_420; 
x_420 = l_Lean_Name_isAnonymous(x_369);
if (x_420 == 0)
{
x_382 = x_369;
goto block_418;
}
else
{
lean_object* x_421; 
lean_dec(x_369);
x_421 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12));
x_382 = x_421;
goto block_418;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_del_object(x_379);
lean_del_object(x_376);
lean_dec(x_375);
lean_del_object(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_422 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_423 = l_Lake_PartialBuildKey_toString(x_2);
x_424 = lean_string_append(x_422, x_423);
lean_dec_ref(x_423);
x_425 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
x_426 = lean_string_append(x_424, x_425);
x_427 = 3;
x_428 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*1, x_427);
x_429 = lean_array_get_size(x_378);
x_430 = lean_array_push(x_378, x_428);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
block_418:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_9, 1);
lean_inc(x_381);
x_384 = l_Lean_Name_append(x_381, x_382);
x_385 = l_Lake_Workspace_findFacetConfig_x3f(x_384, x_383);
if (lean_obj_tag(x_385) == 1)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec_ref(x_2);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec_ref(x_385);
x_387 = lean_ctor_get(x_386, 2);
lean_inc(x_387);
lean_dec(x_386);
lean_inc(x_384);
lean_inc(x_381);
lean_inc_ref(x_368);
x_388 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 11, 3);
lean_closure_set(x_388, 0, x_368);
lean_closure_set(x_388, 1, x_381);
lean_closure_set(x_388, 2, x_384);
x_389 = lean_unsigned_to_nat(0u);
x_390 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
x_391 = l_Lake_Job_bindM___redArg(x_387, x_375, x_388, x_389, x_372, x_5, x_6, x_7, x_8, x_9, x_390);
if (x_371 == 0)
{
lean_ctor_set(x_370, 1, x_384);
x_392 = x_370;
goto block_399;
}
else
{
lean_object* x_400; 
x_400 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_400, 0, x_368);
lean_ctor_set(x_400, 1, x_384);
x_392 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_393; 
if (x_377 == 0)
{
lean_ctor_set(x_376, 1, x_391);
lean_ctor_set(x_376, 0, x_392);
x_393 = x_376;
goto block_397;
}
else
{
lean_object* x_398; 
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_392);
lean_ctor_set(x_398, 1, x_391);
x_393 = x_398;
goto block_397;
}
block_397:
{
lean_object* x_394; 
if (x_380 == 0)
{
lean_ctor_set(x_379, 0, x_393);
x_394 = x_379;
goto block_395;
}
else
{
lean_object* x_396; 
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_378);
x_394 = x_396;
goto block_395;
}
block_395:
{
return x_394;
}
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_385);
lean_del_object(x_376);
lean_dec(x_375);
lean_del_object(x_370);
lean_dec_ref(x_368);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_401 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_402 = l_Lake_PartialBuildKey_toString(x_2);
x_403 = lean_string_append(x_401, x_402);
lean_dec_ref(x_402);
x_404 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
x_405 = lean_string_append(x_403, x_404);
x_406 = 1;
x_407 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_384, x_406);
x_408 = lean_string_append(x_405, x_407);
lean_dec_ref(x_407);
x_409 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_410 = lean_string_append(x_408, x_409);
x_411 = 3;
x_412 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set_uint8(x_412, sizeof(void*)*1, x_411);
x_413 = lean_array_get_size(x_378);
x_414 = lean_array_push(x_378, x_412);
if (x_380 == 0)
{
lean_ctor_set_tag(x_379, 1);
lean_ctor_set(x_379, 1, x_414);
lean_ctor_set(x_379, 0, x_413);
x_415 = x_379;
goto block_416;
}
else
{
lean_object* x_417; 
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_413);
lean_ctor_set(x_417, 1, x_414);
x_415 = x_417;
goto block_416;
}
block_416:
{
return x_415;
}
}
}
}
}
}
else
{
lean_del_object(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_373;
}
}
}
}
block_16:
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
block_26:
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
x_13 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc_ref(x_2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_PartialBuildKey_fetchInCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc_ref(x_2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
x_14 = x_11;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lake_Job_toOpaque___redArg(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_13);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
x_25 = x_11;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_PartialBuildKey_fetchIn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_46; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 1);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_46 = !lean_is_exclusive(x_10);
if (x_46 == 0)
{
x_17 = x_10;
x_18 = x_46;
goto block_45;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_12);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_3);
x_20 = lean_apply_7(x_5, x_19, x_6, x_7, x_8, x_9, x_12, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_32; 
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
x_23 = x_20;
x_24 = x_32;
goto block_31;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_25; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_22);
x_25 = x_17;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_16);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_14);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_44; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
x_35 = x_20;
x_36 = x_44;
goto block_43;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_box(0);
x_36 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_37; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_34);
x_37 = x_17;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_15);
lean_ctor_set(x_42, 2, x_16);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_42, sizeof(void*)*3 + 1, x_14);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_instDataKindModule;
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec_ref(x_7);
lean_inc(x_11);
x_13 = l_Lake_Workspace_findModule_x3f(x_11, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_16 = 0;
x_17 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_task_pure(x_18);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
x_22 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_23 = l_Lake_BuildKey_toString(x_1);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
x_26 = lean_string_append(x_24, x_25);
x_27 = 1;
x_28 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_11, x_27);
x_29 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
x_30 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_31 = lean_string_append(x_29, x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_8);
x_35 = lean_array_push(x_8, x_33);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_dec_ref(x_7);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec_ref(x_2);
x_39 = lean_ctor_get(x_37, 6);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_39, x_38);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_38);
lean_dec_ref(x_1);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lake_instDataKindPackage;
x_43 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_44 = 0;
x_45 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_task_pure(x_46);
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_8);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_40);
x_50 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_51 = l_Lake_BuildKey_toString(x_1);
x_52 = lean_string_append(x_50, x_51);
lean_dec_ref(x_51);
x_53 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_54 = lean_string_append(x_52, x_53);
x_55 = 1;
x_56 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_38, x_55);
x_57 = lean_string_append(x_54, x_56);
lean_dec_ref(x_56);
x_58 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_59 = lean_string_append(x_57, x_58);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_get_size(x_8);
x_63 = lean_array_push(x_8, x_61);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
case 2:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_125; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_dec_ref(x_7);
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
x_125 = !lean_is_exclusive(x_2);
if (x_125 == 0)
{
x_68 = x_2;
x_69 = x_125;
goto block_124;
}
else
{
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_65, 6);
lean_inc(x_70);
lean_dec(x_65);
x_71 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_70, x_66);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
lean_inc(x_72);
lean_inc(x_67);
x_73 = l_Lake_Package_findTargetModule_x3f(x_67, x_72);
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_72);
lean_dec(x_67);
lean_dec_ref(x_1);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_76 = 0;
x_77 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
if (x_69 == 0)
{
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 1, x_77);
lean_ctor_set(x_68, 0, x_74);
x_78 = x_68;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_77);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_task_pure(x_78);
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_10);
lean_ctor_set(x_80, 2, x_75);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_76);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_8);
return x_81;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_73);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
lean_dec(x_72);
x_85 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_86 = l_Lake_BuildKey_toString(x_1);
x_87 = lean_string_append(x_85, x_86);
lean_dec_ref(x_86);
x_88 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
x_89 = lean_string_append(x_87, x_88);
x_90 = 1;
x_91 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_67, x_90);
x_92 = lean_string_append(x_89, x_91);
lean_dec_ref(x_91);
x_93 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
x_94 = lean_string_append(x_92, x_93);
x_95 = 0;
x_96 = l_Lean_Name_toString(x_84, x_95);
x_97 = lean_string_append(x_94, x_96);
lean_dec_ref(x_96);
x_98 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_99 = lean_string_append(x_97, x_98);
x_100 = 3;
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
x_102 = lean_array_get_size(x_8);
x_103 = lean_array_push(x_8, x_101);
if (x_69 == 0)
{
lean_ctor_set_tag(x_68, 1);
lean_ctor_set(x_68, 1, x_103);
lean_ctor_set(x_68, 0, x_102);
x_104 = x_68;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_103);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_71);
lean_dec(x_67);
x_107 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_108 = l_Lake_BuildKey_toString(x_1);
x_109 = lean_string_append(x_107, x_108);
lean_dec_ref(x_108);
x_110 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_111 = lean_string_append(x_109, x_110);
x_112 = 1;
x_113 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_66, x_112);
x_114 = lean_string_append(x_111, x_113);
lean_dec_ref(x_113);
x_115 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_116 = lean_string_append(x_114, x_115);
x_117 = 3;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
x_119 = lean_array_get_size(x_8);
x_120 = lean_array_push(x_8, x_118);
if (x_69 == 0)
{
lean_ctor_set_tag(x_68, 1);
lean_ctor_set(x_68, 1, x_120);
lean_ctor_set(x_68, 0, x_119);
x_121 = x_68;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_120);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
case 3:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_156; 
x_126 = lean_ctor_get(x_7, 1);
x_127 = lean_ctor_get(x_2, 0);
x_128 = lean_ctor_get(x_2, 1);
x_156 = !lean_is_exclusive(x_2);
if (x_156 == 0)
{
x_129 = x_2;
x_130 = x_156;
goto block_155;
}
else
{
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_2);
x_129 = lean_box(0);
x_130 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_126, 6);
x_132 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_131, x_127);
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_127);
lean_dec_ref(x_1);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
if (x_130 == 0)
{
lean_ctor_set_tag(x_129, 0);
lean_ctor_set(x_129, 0, x_133);
x_134 = x_129;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_128);
x_134 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_135; 
x_135 = lean_apply_7(x_3, x_134, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_135;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_132);
lean_dec(x_128);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_138 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_139 = l_Lake_BuildKey_toString(x_1);
x_140 = lean_string_append(x_138, x_139);
lean_dec_ref(x_139);
x_141 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_142 = lean_string_append(x_140, x_141);
x_143 = 1;
x_144 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_127, x_143);
x_145 = lean_string_append(x_142, x_144);
lean_dec_ref(x_144);
x_146 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_147 = lean_string_append(x_145, x_146);
x_148 = 3;
x_149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_148);
x_150 = lean_array_get_size(x_8);
x_151 = lean_array_push(x_8, x_149);
if (x_130 == 0)
{
lean_ctor_set_tag(x_129, 1);
lean_ctor_set(x_129, 1, x_151);
lean_ctor_set(x_129, 0, x_150);
x_152 = x_129;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_151);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
default: 
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_2, 0);
x_158 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_157);
lean_inc_ref(x_1);
x_159 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_1, x_157, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_207; 
x_160 = lean_ctor_get(x_159, 0);
x_161 = lean_ctor_get(x_159, 1);
x_207 = !lean_is_exclusive(x_159);
if (x_207 == 0)
{
x_162 = x_159;
x_163 = x_207;
goto block_206;
}
else
{
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_159);
x_162 = lean_box(0);
x_163 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_160, 1);
x_165 = l_Lean_Name_isAnonymous(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_inc(x_158);
lean_inc_ref(x_157);
lean_dec_ref(x_2);
x_166 = lean_ctor_get(x_7, 1);
x_167 = l_Lake_Workspace_findFacetConfig_x3f(x_158, x_166);
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_1);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
lean_dec(x_168);
lean_inc(x_164);
x_170 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed), 11, 3);
lean_closure_set(x_170, 0, x_157);
lean_closure_set(x_170, 1, x_164);
lean_closure_set(x_170, 2, x_158);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
x_173 = l_Lake_Job_bindM___redArg(x_169, x_160, x_170, x_171, x_165, x_3, x_4, x_5, x_6, x_7, x_172);
if (x_163 == 0)
{
lean_ctor_set(x_162, 0, x_173);
x_174 = x_162;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_161);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_167);
lean_dec(x_160);
lean_dec_ref(x_157);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_177 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_178 = l_Lake_BuildKey_toString(x_1);
x_179 = lean_string_append(x_177, x_178);
lean_dec_ref(x_178);
x_180 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
x_181 = lean_string_append(x_179, x_180);
x_182 = 1;
x_183 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_158, x_182);
x_184 = lean_string_append(x_181, x_183);
lean_dec_ref(x_183);
x_185 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_186 = lean_string_append(x_184, x_185);
x_187 = 3;
x_188 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*1, x_187);
x_189 = lean_array_get_size(x_161);
x_190 = lean_array_push(x_161, x_188);
if (x_163 == 0)
{
lean_ctor_set_tag(x_162, 1);
lean_ctor_set(x_162, 1, x_190);
lean_ctor_set(x_162, 0, x_189);
x_191 = x_162;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_189);
lean_ctor_set(x_193, 1, x_190);
x_191 = x_193;
goto block_192;
}
block_192:
{
return x_191;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_160);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_194 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_195 = l_Lake_BuildKey_toString(x_2);
x_196 = lean_string_append(x_194, x_195);
lean_dec_ref(x_195);
x_197 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
x_198 = lean_string_append(x_196, x_197);
x_199 = 3;
x_200 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_199);
x_201 = lean_array_get_size(x_161);
x_202 = lean_array_push(x_161, x_200);
if (x_163 == 0)
{
lean_ctor_set_tag(x_162, 1);
lean_ctor_set(x_162, 1, x_202);
lean_ctor_set(x_162, 0, x_201);
x_203 = x_162;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_202);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_159;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_BuildKey_fetch___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_2, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_BuildKey_fetch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_inc_ref_n(x_3, 2);
x_12 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_2, x_3, x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_54; 
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
x_15 = x_12;
x_16 = x_54;
goto block_53;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_17; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_51; 
x_36 = lean_ctor_get(x_13, 1);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_13, 0);
lean_dec(x_52);
x_37 = x_13;
x_38 = x_51;
goto block_50;
}
else
{
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_box(0);
x_38 = x_51;
goto block_50;
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__0));
x_19 = l_Lake_PartialBuildKey_toString(x_3);
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__1));
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_11);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__2));
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_17);
lean_dec_ref(x_17);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_14);
x_31 = lean_array_push(x_14, x_29);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_31);
lean_ctor_set(x_15, 0, x_30);
x_32 = x_15;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
block_50:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_name_eq(x_39, x_1);
if (x_40 == 0)
{
uint8_t x_41; 
lean_inc(x_39);
lean_del_object(x_37);
lean_dec(x_36);
x_41 = l_Lean_Name_isAnonymous(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_43 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_39, x_11);
x_44 = lean_string_append(x_42, x_43);
lean_dec_ref(x_43);
x_45 = lean_string_append(x_44, x_42);
x_17 = x_45;
goto block_35;
}
else
{
lean_object* x_46; 
lean_dec(x_39);
x_46 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__3));
x_17 = x_46;
goto block_35;
}
}
else
{
lean_object* x_47; 
lean_del_object(x_15);
lean_dec_ref(x_3);
lean_dec(x_1);
if (x_38 == 0)
{
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_36);
x_47 = x_37;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_14);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
x_63 = !lean_is_exclusive(x_12);
if (x_63 == 0)
{
x_57 = x_12;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Target_fetchIn___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_Target_fetchIn___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_Target_fetchIn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Target_fetchIn___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_TargetArray_fetchIn___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lake_TargetArray_fetchIn___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_68; 
x_12 = lean_obj_once(&l_Lake_TargetArray_fetchIn___redArg___closed__0, &l_Lake_TargetArray_fetchIn___redArg___closed__0_once, _init_l_Lake_TargetArray_fetchIn___redArg___closed__0);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_68 = !lean_is_exclusive(x_12);
if (x_68 == 0)
{
x_15 = x_12;
x_16 = x_68;
goto block_67;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_63; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_63 = !lean_is_exclusive(x_13);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_13, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_13, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_13, 2);
lean_dec(x_66);
x_19 = x_13;
x_20 = x_63;
goto block_62;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_inc(x_14);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_14);
lean_inc(x_14);
lean_inc(x_18);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_14);
lean_inc_ref(x_22);
lean_inc(x_18);
x_24 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_22);
lean_inc(x_18);
lean_inc_ref(x_17);
x_25 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_18);
lean_closure_set(x_25, 2, x_14);
x_26 = l_Lake_EStateT_instFunctor___redArg(x_17);
x_27 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_27, 0, x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_23);
lean_ctor_set(x_19, 3, x_24);
lean_ctor_set(x_19, 2, x_25);
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_26);
x_28 = x_19;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_26);
lean_ctor_set(x_61, 1, x_27);
lean_ctor_set(x_61, 2, x_25);
lean_ctor_set(x_61, 3, x_24);
lean_ctor_set(x_61, 4, x_23);
x_28 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_29; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_22);
lean_ctor_set(x_15, 0, x_28);
x_29 = x_15;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_28);
lean_ctor_set(x_59, 1, x_22);
x_29 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = l_ReaderT_instMonad___redArg(x_31);
x_33 = l_ReaderT_instMonad___redArg(x_32);
x_34 = l_Lake_EquipT_instMonad___redArg(x_33);
x_35 = lean_array_size(x_3);
x_36 = 0;
x_37 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_34, x_21, x_35, x_36, x_3);
x_38 = lean_apply_7(x_37, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_48; 
x_39 = lean_ctor_get(x_38, 0);
x_40 = lean_ctor_get(x_38, 1);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
x_41 = x_38;
x_42 = x_48;
goto block_47;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lake_Job_collectArray___redArg(x_39, x_4);
lean_dec(x_39);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_43);
x_44 = x_41;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_40);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec_ref(x_4);
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
x_51 = x_38;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_TargetArray_fetchIn___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_TargetArray_fetchIn___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_TargetArray_fetchIn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
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
res = runtime_initialize_Lake_Build_Infos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Key(builtin)
;
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
res = initialize_Lake_Build_Infos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Key(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Target_Fetch(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Target_Fetch(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Target_Fetch(builtin);
}
#ifdef __cplusplus
}
#endif
