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
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value;
static const lean_string_object l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2 = (const lean_object*)&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value;
lean_object* l_Lake_BuildTrace_nil(lean_object*);
static lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3;
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
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
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_dec(x_58);
if (lean_obj_tag(x_57) == 0)
{
lean_free_object(x_55);
x_7 = x_5;
x_8 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec_ref(x_57);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_60; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_ctor_set(x_55, 1, x_5);
lean_ctor_set(x_55, 0, x_60);
return x_55;
}
else
{
lean_dec(x_59);
lean_free_object(x_55);
x_7 = x_5;
x_8 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
lean_dec(x_55);
if (lean_obj_tag(x_61) == 0)
{
x_7 = x_5;
x_8 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_5);
return x_64;
}
else
{
lean_dec(x_62);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
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
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_dec(x_62);
if (lean_obj_tag(x_61) == 0)
{
lean_free_object(x_59);
x_11 = x_9;
x_12 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec_ref(x_61);
if (lean_obj_tag(x_63) == 1)
{
lean_object* x_64; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
lean_ctor_set(x_59, 1, x_9);
lean_ctor_set(x_59, 0, x_64);
return x_59;
}
else
{
lean_dec(x_63);
lean_free_object(x_59);
x_11 = x_9;
x_12 = lean_box(0);
goto block_28;
}
}
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
if (lean_obj_tag(x_65) == 0)
{
x_11 = x_9;
x_12 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_9);
return x_68;
}
else
{
lean_dec(x_66);
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_3);
x_15 = lean_apply_7(x_5, x_14, x_6, x_7, x_8, x_9, x_13, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_10, 0, x_17);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_28 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 1);
x_29 = lean_ctor_get(x_10, 1);
x_30 = lean_ctor_get(x_10, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_26);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set(x_31, 3, x_3);
x_32 = lean_apply_7(x_5, x_31, x_6, x_7, x_8, x_9, x_26, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*3 + 1, x_28);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*3 + 1, x_28);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_7);
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
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2));
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3;
x_3 = 0;
x_4 = 0;
x_5 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0;
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
x_38 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_60 = x_3;
} else {
 lean_dec_ref(x_3);
 x_60 = lean_box(0);
}
x_78 = l_Lake_instDataKindPackage;
switch (lean_obj_tag(x_59)) {
case 0:
{
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_79 = x_1;
x_80 = x_10;
x_81 = lean_box(0);
goto block_92;
}
case 2:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_9, 1);
lean_inc(x_93);
lean_dec_ref(x_9);
x_94 = lean_ctor_get(x_93, 6);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_94, x_59);
lean_dec(x_94);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; 
lean_dec_ref(x_59);
lean_dec_ref(x_2);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_79 = x_96;
x_80 = x_10;
x_81 = lean_box(0);
goto block_92;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_95);
lean_dec(x_60);
x_97 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_98 = l_Lake_PartialBuildKey_toString(x_2);
x_99 = lean_string_append(x_97, x_98);
lean_dec_ref(x_98);
x_100 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_101 = lean_string_append(x_99, x_100);
x_102 = 1;
x_103 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_59, x_102);
x_104 = lean_string_append(x_101, x_103);
lean_dec_ref(x_103);
x_105 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_106 = lean_string_append(x_104, x_105);
x_107 = 3;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_get_size(x_10);
x_110 = lean_array_push(x_10, x_108);
x_22 = x_109;
x_23 = x_110;
x_24 = lean_box(0);
goto block_26;
}
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_9, 1);
lean_inc(x_111);
lean_dec_ref(x_9);
x_112 = lean_ctor_get(x_111, 5);
lean_inc_ref(x_112);
lean_dec(x_111);
x_113 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_114 = lean_array_size(x_112);
x_115 = 0;
x_116 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_59, x_112, x_114, x_115, x_113);
lean_dec_ref(x_112);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_dec(x_60);
x_61 = x_10;
x_62 = lean_box(0);
goto block_77;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
if (lean_obj_tag(x_118) == 1)
{
lean_object* x_119; 
lean_dec(x_59);
lean_dec_ref(x_2);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_79 = x_119;
x_80 = x_10;
x_81 = lean_box(0);
goto block_92;
}
else
{
lean_dec(x_118);
lean_dec(x_60);
x_61 = x_10;
x_62 = lean_box(0);
goto block_77;
}
}
}
}
block_77:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_64 = l_Lake_PartialBuildKey_toString(x_2);
x_65 = lean_string_append(x_63, x_64);
lean_dec_ref(x_64);
x_66 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_67 = lean_string_append(x_65, x_66);
x_68 = 1;
x_69 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_59, x_68);
x_70 = lean_string_append(x_67, x_69);
lean_dec_ref(x_69);
x_71 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_72 = lean_string_append(x_70, x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_array_get_size(x_61);
x_76 = lean_array_push(x_61, x_74);
x_22 = x_75;
x_23 = x_76;
x_24 = lean_box(0);
goto block_26;
}
block_92:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_ctor_get(x_79, 2);
lean_inc(x_82);
if (lean_is_scalar(x_60)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_60;
}
lean_ctor_set(x_83, 0, x_82);
x_84 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_85 = 0;
x_86 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_task_pure(x_87);
x_89 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
lean_ctor_set(x_89, 2, x_84);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
return x_91;
}
}
case 2:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_160; lean_object* x_161; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_120 = lean_ctor_get(x_3, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_122 = x_3;
} else {
 lean_dec_ref(x_3);
 x_122 = lean_box(0);
}
switch (lean_obj_tag(x_120)) {
case 0:
{
lean_dec_ref(x_9);
x_123 = x_1;
x_124 = x_10;
x_125 = lean_box(0);
goto block_159;
}
case 2:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec_ref(x_1);
x_177 = lean_ctor_get(x_9, 1);
lean_inc(x_177);
lean_dec_ref(x_9);
x_178 = lean_ctor_get(x_177, 6);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_178, x_120);
lean_dec(x_178);
if (lean_obj_tag(x_179) == 1)
{
lean_object* x_180; 
lean_dec_ref(x_120);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_123 = x_180;
x_124 = x_10;
x_125 = lean_box(0);
goto block_159;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_179);
lean_dec(x_122);
lean_dec(x_121);
x_181 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_182 = l_Lake_PartialBuildKey_toString(x_2);
x_183 = lean_string_append(x_181, x_182);
lean_dec_ref(x_182);
x_184 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_185 = lean_string_append(x_183, x_184);
x_186 = 1;
x_187 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_120, x_186);
x_188 = lean_string_append(x_185, x_187);
lean_dec_ref(x_187);
x_189 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_190 = lean_string_append(x_188, x_189);
x_191 = 3;
x_192 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_191);
x_193 = lean_array_get_size(x_10);
x_194 = lean_array_push(x_10, x_192);
x_17 = x_193;
x_18 = x_194;
x_19 = lean_box(0);
goto block_21;
}
}
default: 
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; size_t x_198; size_t x_199; lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_9, 1);
lean_inc(x_195);
lean_dec_ref(x_9);
x_196 = lean_ctor_get(x_195, 5);
lean_inc_ref(x_196);
lean_dec(x_195);
x_197 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_198 = lean_array_size(x_196);
x_199 = 0;
x_200 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_120, x_196, x_198, x_199, x_197);
lean_dec_ref(x_196);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_dec(x_122);
lean_dec(x_121);
x_160 = x_10;
x_161 = lean_box(0);
goto block_176;
}
else
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
if (lean_obj_tag(x_202) == 1)
{
lean_object* x_203; 
lean_dec(x_120);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
x_123 = x_203;
x_124 = x_10;
x_125 = lean_box(0);
goto block_159;
}
else
{
lean_dec(x_202);
lean_dec(x_122);
lean_dec(x_121);
x_160 = x_10;
x_161 = lean_box(0);
goto block_176;
}
}
}
}
block_159:
{
lean_object* x_126; 
lean_inc_ref(x_123);
lean_inc(x_121);
x_126 = l_Lake_Package_findTargetModule_x3f(x_121, x_123);
if (lean_obj_tag(x_126) == 1)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec_ref(x_2);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_ctor_get(x_123, 2);
lean_inc(x_128);
lean_dec_ref(x_123);
if (lean_is_scalar(x_122)) {
 x_129 = lean_alloc_ctor(2, 2, 0);
} else {
 x_129 = x_122;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_121);
x_130 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_131 = 0;
x_132 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_task_pure(x_133);
x_135 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_27);
lean_ctor_set(x_135, 2, x_130);
lean_ctor_set_uint8(x_135, sizeof(void*)*3, x_131);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_124);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_126);
lean_dec(x_122);
x_138 = lean_ctor_get(x_123, 1);
lean_inc(x_138);
lean_dec_ref(x_123);
x_139 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_140 = l_Lake_PartialBuildKey_toString(x_2);
x_141 = lean_string_append(x_139, x_140);
lean_dec_ref(x_140);
x_142 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6));
x_143 = lean_string_append(x_141, x_142);
x_144 = 1;
x_145 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_121, x_144);
x_146 = lean_string_append(x_143, x_145);
lean_dec_ref(x_145);
x_147 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
x_148 = lean_string_append(x_146, x_147);
x_149 = 0;
x_150 = l_Lean_Name_toString(x_138, x_149);
x_151 = lean_string_append(x_148, x_150);
lean_dec_ref(x_150);
x_152 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_153 = lean_string_append(x_151, x_152);
x_154 = 3;
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_array_get_size(x_124);
x_157 = lean_array_push(x_124, x_155);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
block_176:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_162 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_163 = l_Lake_PartialBuildKey_toString(x_2);
x_164 = lean_string_append(x_162, x_163);
lean_dec_ref(x_163);
x_165 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_166 = lean_string_append(x_164, x_165);
x_167 = 1;
x_168 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_120, x_167);
x_169 = lean_string_append(x_166, x_168);
lean_dec_ref(x_168);
x_170 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_171 = lean_string_append(x_169, x_170);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_get_size(x_160);
x_175 = lean_array_push(x_160, x_173);
x_17 = x_174;
x_18 = x_175;
x_19 = lean_box(0);
goto block_21;
}
}
case 3:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_310; lean_object* x_311; 
x_204 = lean_ctor_get(x_3, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_3, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_206 = x_3;
} else {
 lean_dec_ref(x_3);
 x_206 = lean_box(0);
}
switch (lean_obj_tag(x_204)) {
case 0:
{
x_207 = x_1;
x_208 = x_10;
x_209 = lean_box(0);
goto block_309;
}
case 2:
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec_ref(x_1);
x_327 = lean_ctor_get(x_9, 1);
x_328 = lean_ctor_get(x_327, 6);
x_329 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_328, x_204);
if (lean_obj_tag(x_329) == 1)
{
lean_object* x_330; 
lean_dec_ref(x_204);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec_ref(x_329);
x_207 = x_330;
x_208 = x_10;
x_209 = lean_box(0);
goto block_309;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_329);
lean_dec(x_206);
lean_dec(x_205);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_331 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_332 = l_Lake_PartialBuildKey_toString(x_2);
x_333 = lean_string_append(x_331, x_332);
lean_dec_ref(x_332);
x_334 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_335 = lean_string_append(x_333, x_334);
x_336 = 1;
x_337 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_204, x_336);
x_338 = lean_string_append(x_335, x_337);
lean_dec_ref(x_337);
x_339 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_340 = lean_string_append(x_338, x_339);
x_341 = 3;
x_342 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*1, x_341);
x_343 = lean_array_get_size(x_10);
x_344 = lean_array_push(x_10, x_342);
x_12 = x_343;
x_13 = x_344;
x_14 = lean_box(0);
goto block_16;
}
}
default: 
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; size_t x_348; size_t x_349; lean_object* x_350; lean_object* x_351; 
lean_dec_ref(x_1);
x_345 = lean_ctor_get(x_9, 1);
x_346 = lean_ctor_get(x_345, 5);
x_347 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_348 = lean_array_size(x_346);
x_349 = 0;
x_350 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_204, x_346, x_348, x_349, x_347);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
if (lean_obj_tag(x_351) == 0)
{
lean_dec(x_206);
lean_dec(x_205);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_310 = x_10;
x_311 = lean_box(0);
goto block_326;
}
else
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
lean_dec_ref(x_351);
if (lean_obj_tag(x_352) == 1)
{
lean_object* x_353; 
lean_dec(x_204);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_207 = x_353;
x_208 = x_10;
x_209 = lean_box(0);
goto block_309;
}
else
{
lean_dec(x_352);
lean_dec(x_206);
lean_dec(x_205);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_310 = x_10;
x_311 = lean_box(0);
goto block_326;
}
}
}
}
block_309:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_207, 1);
x_211 = lean_ctor_get(x_207, 2);
lean_inc(x_205);
lean_inc(x_211);
if (lean_is_scalar(x_206)) {
 x_212 = lean_alloc_ctor(3, 2, 0);
} else {
 x_212 = x_206;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_205);
if (x_4 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_2);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_207);
lean_ctor_set(x_213, 1, x_205);
x_214 = lean_apply_7(x_5, x_213, x_6, x_7, x_8, x_9, x_208, lean_box(0));
if (lean_obj_tag(x_214) == 0)
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_216);
lean_ctor_set(x_214, 0, x_217);
return x_214;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_214, 0);
x_219 = lean_ctor_get(x_214, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_214);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_212);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
uint8_t x_222; 
lean_dec_ref(x_212);
x_222 = !lean_is_exclusive(x_214);
if (x_222 == 0)
{
return x_214;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_214, 0);
x_224 = lean_ctor_get(x_214, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_214);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; 
x_226 = l_Lake_Package_findTargetDecl_x3f(x_205, x_207);
if (lean_obj_tag(x_226) == 1)
{
lean_object* x_227; uint8_t x_228; 
lean_dec_ref(x_2);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_229 = lean_ctor_get(x_227, 1);
x_230 = lean_ctor_get(x_227, 2);
x_231 = lean_ctor_get(x_227, 3);
x_232 = lean_ctor_get(x_227, 0);
lean_dec(x_232);
x_233 = l_Lean_Name_isAnonymous(x_230);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_205);
x_234 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9));
lean_inc(x_230);
x_235 = l_Lean_Name_str___override(x_230, x_234);
x_236 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_236, 0, x_207);
lean_ctor_set(x_236, 1, x_229);
lean_ctor_set(x_236, 2, x_231);
lean_inc(x_235);
lean_inc_ref(x_212);
lean_ctor_set_tag(x_227, 1);
lean_ctor_set(x_227, 3, x_235);
lean_ctor_set(x_227, 2, x_236);
lean_ctor_set(x_227, 1, x_230);
lean_ctor_set(x_227, 0, x_212);
x_237 = lean_apply_7(x_5, x_227, x_6, x_7, x_8, x_9, x_208, lean_box(0));
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_240, 0, x_212);
lean_ctor_set(x_240, 1, x_235);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
lean_ctor_set(x_237, 0, x_241);
return x_237;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_237, 0);
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_237);
x_244 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_244, 0, x_212);
lean_ctor_set(x_244, 1, x_235);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_dec(x_235);
lean_dec_ref(x_212);
x_247 = !lean_is_exclusive(x_237);
if (x_247 == 0)
{
return x_237;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_237, 0);
x_249 = lean_ctor_get(x_237, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_237);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_free_object(x_227);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_207);
lean_ctor_set(x_251, 1, x_205);
x_252 = lean_apply_7(x_5, x_251, x_6, x_7, x_8, x_9, x_208, lean_box(0));
if (lean_obj_tag(x_252) == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_252, 0);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_212);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_252, 0, x_255);
return x_252;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_252, 0);
x_257 = lean_ctor_get(x_252, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_252);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_212);
lean_ctor_set(x_258, 1, x_256);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
uint8_t x_260; 
lean_dec_ref(x_212);
x_260 = !lean_is_exclusive(x_252);
if (x_260 == 0)
{
return x_252;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_252, 0);
x_262 = lean_ctor_get(x_252, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_252);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_264 = lean_ctor_get(x_227, 1);
x_265 = lean_ctor_get(x_227, 2);
x_266 = lean_ctor_get(x_227, 3);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_227);
x_267 = l_Lean_Name_isAnonymous(x_265);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_205);
x_268 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9));
lean_inc(x_265);
x_269 = l_Lean_Name_str___override(x_265, x_268);
x_270 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_270, 0, x_207);
lean_ctor_set(x_270, 1, x_264);
lean_ctor_set(x_270, 2, x_266);
lean_inc(x_269);
lean_inc_ref(x_212);
x_271 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_271, 0, x_212);
lean_ctor_set(x_271, 1, x_265);
lean_ctor_set(x_271, 2, x_270);
lean_ctor_set(x_271, 3, x_269);
x_272 = lean_apply_7(x_5, x_271, x_6, x_7, x_8, x_9, x_208, lean_box(0));
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_276, 0, x_212);
lean_ctor_set(x_276, 1, x_269);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_273);
if (lean_is_scalar(x_275)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_275;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_274);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_269);
lean_dec_ref(x_212);
x_279 = lean_ctor_get(x_272, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_272, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_281 = x_272;
} else {
 lean_dec_ref(x_272);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_207);
lean_ctor_set(x_283, 1, x_205);
x_284 = lean_apply_7(x_5, x_283, x_6, x_7, x_8, x_9, x_208, lean_box(0));
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_212);
lean_ctor_set(x_288, 1, x_285);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec_ref(x_212);
x_290 = lean_ctor_get(x_284, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_284, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_292 = x_284;
} else {
 lean_dec_ref(x_284);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_inc(x_210);
lean_dec(x_226);
lean_dec_ref(x_212);
lean_dec_ref(x_207);
lean_dec(x_205);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_294 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_295 = l_Lake_PartialBuildKey_toString(x_2);
x_296 = lean_string_append(x_294, x_295);
lean_dec_ref(x_295);
x_297 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10));
x_298 = lean_string_append(x_296, x_297);
x_299 = 0;
x_300 = l_Lean_Name_toString(x_210, x_299);
x_301 = lean_string_append(x_298, x_300);
lean_dec_ref(x_300);
x_302 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_303 = lean_string_append(x_301, x_302);
x_304 = 3;
x_305 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set_uint8(x_305, sizeof(void*)*1, x_304);
x_306 = lean_array_get_size(x_208);
x_307 = lean_array_push(x_208, x_305);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
block_326:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_312 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_313 = l_Lake_PartialBuildKey_toString(x_2);
x_314 = lean_string_append(x_312, x_313);
lean_dec_ref(x_313);
x_315 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_316 = lean_string_append(x_314, x_315);
x_317 = 1;
x_318 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_204, x_317);
x_319 = lean_string_append(x_316, x_318);
lean_dec_ref(x_318);
x_320 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_321 = lean_string_append(x_319, x_320);
x_322 = 3;
x_323 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*1, x_322);
x_324 = lean_array_get_size(x_310);
x_325 = lean_array_push(x_310, x_323);
x_12 = x_324;
x_13 = x_325;
x_14 = lean_box(0);
goto block_16;
}
}
default: 
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; 
x_354 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_354);
x_355 = lean_ctor_get(x_3, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_356 = x_3;
} else {
 lean_dec_ref(x_3);
 x_356 = lean_box(0);
}
x_357 = 0;
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_354);
lean_inc_ref(x_2);
x_358 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_354, x_357, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_394; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_361 = x_359;
} else {
 lean_dec_ref(x_359);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_358, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_363 = x_358;
} else {
 lean_dec_ref(x_358);
 x_363 = lean_box(0);
}
x_364 = lean_ctor_get(x_360, 1);
x_394 = l_Lean_Name_isAnonymous(x_364);
if (x_394 == 0)
{
uint8_t x_395; 
x_395 = l_Lean_Name_isAnonymous(x_355);
if (x_395 == 0)
{
x_365 = x_355;
goto block_393;
}
else
{
lean_object* x_396; 
lean_dec(x_355);
x_396 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12));
x_365 = x_396;
goto block_393;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_397 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_398 = l_Lake_PartialBuildKey_toString(x_2);
x_399 = lean_string_append(x_397, x_398);
lean_dec_ref(x_398);
x_400 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
x_401 = lean_string_append(x_399, x_400);
x_402 = 3;
x_403 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set_uint8(x_403, sizeof(void*)*1, x_402);
x_404 = lean_array_get_size(x_362);
x_405 = lean_array_push(x_362, x_403);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
block_393:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_9, 1);
lean_inc(x_364);
x_367 = l_Lean_Name_append(x_364, x_365);
x_368 = l_Lake_Workspace_findFacetConfig_x3f(x_367, x_366);
if (lean_obj_tag(x_368) == 1)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec_ref(x_2);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec_ref(x_368);
x_370 = lean_ctor_get(x_369, 2);
lean_inc(x_370);
lean_dec(x_369);
lean_inc(x_367);
lean_inc(x_364);
lean_inc_ref(x_354);
x_371 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 11, 3);
lean_closure_set(x_371, 0, x_354);
lean_closure_set(x_371, 1, x_364);
lean_closure_set(x_371, 2, x_367);
x_372 = lean_unsigned_to_nat(0u);
x_373 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3;
x_374 = l_Lake_Job_bindM___redArg(x_370, x_360, x_371, x_372, x_357, x_5, x_6, x_7, x_8, x_9, x_373);
if (lean_is_scalar(x_356)) {
 x_375 = lean_alloc_ctor(4, 2, 0);
} else {
 x_375 = x_356;
}
lean_ctor_set(x_375, 0, x_354);
lean_ctor_set(x_375, 1, x_367);
if (lean_is_scalar(x_361)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_361;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
if (lean_is_scalar(x_363)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_363;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_362);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_368);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_356);
lean_dec_ref(x_354);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_378 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_379 = l_Lake_PartialBuildKey_toString(x_2);
x_380 = lean_string_append(x_378, x_379);
lean_dec_ref(x_379);
x_381 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
x_382 = lean_string_append(x_380, x_381);
x_383 = 1;
x_384 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_367, x_383);
x_385 = lean_string_append(x_382, x_384);
lean_dec_ref(x_384);
x_386 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_387 = lean_string_append(x_385, x_386);
x_388 = 3;
x_389 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set_uint8(x_389, sizeof(void*)*1, x_388);
x_390 = lean_array_get_size(x_362);
x_391 = lean_array_push(x_362, x_389);
if (lean_is_scalar(x_363)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_363;
 lean_ctor_set_tag(x_392, 1);
}
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
lean_dec(x_356);
lean_dec(x_355);
lean_dec_ref(x_354);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_358;
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lake_Job_toOpaque___redArg(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lake_Job_toOpaque___redArg(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_3);
x_15 = lean_apply_7(x_5, x_14, x_6, x_7, x_8, x_9, x_13, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_10, 0, x_17);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_15, 1);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_24);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_28 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 1);
x_29 = lean_ctor_get(x_10, 1);
x_30 = lean_ctor_get(x_10, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_26);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set(x_31, 3, x_3);
x_32 = lean_apply_7(x_5, x_31, x_6, x_7, x_8, x_9, x_26, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*3 + 1, x_28);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*3 + 1, x_28);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
x_17 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
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
x_45 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
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
lean_object* x_65; uint8_t x_66; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_dec_ref(x_7);
x_66 = !lean_is_exclusive(x_2);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_69 = lean_ctor_get(x_65, 6);
lean_inc(x_69);
lean_dec(x_65);
x_70 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_69, x_67);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 1)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
lean_inc(x_71);
lean_inc(x_68);
x_72 = l_Lake_Package_findTargetModule_x3f(x_68, x_71);
if (lean_obj_tag(x_72) == 1)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_75 = 0;
x_76 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_76);
lean_ctor_set(x_2, 0, x_73);
x_77 = lean_task_pure(x_2);
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_10);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_8);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_72);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_dec(x_71);
x_81 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_82 = l_Lake_BuildKey_toString(x_1);
x_83 = lean_string_append(x_81, x_82);
lean_dec_ref(x_82);
x_84 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
x_85 = lean_string_append(x_83, x_84);
x_86 = 1;
x_87 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_68, x_86);
x_88 = lean_string_append(x_85, x_87);
lean_dec_ref(x_87);
x_89 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
x_90 = lean_string_append(x_88, x_89);
x_91 = 0;
x_92 = l_Lean_Name_toString(x_80, x_91);
x_93 = lean_string_append(x_90, x_92);
lean_dec_ref(x_92);
x_94 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_95 = lean_string_append(x_93, x_94);
x_96 = 3;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_array_get_size(x_8);
x_99 = lean_array_push(x_8, x_97);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_99);
lean_ctor_set(x_2, 0, x_98);
return x_2;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_70);
lean_dec(x_68);
x_100 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_101 = l_Lake_BuildKey_toString(x_1);
x_102 = lean_string_append(x_100, x_101);
lean_dec_ref(x_101);
x_103 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_104 = lean_string_append(x_102, x_103);
x_105 = 1;
x_106 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_67, x_105);
x_107 = lean_string_append(x_104, x_106);
lean_dec_ref(x_106);
x_108 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_109 = lean_string_append(x_107, x_108);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_get_size(x_8);
x_113 = lean_array_push(x_8, x_111);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_113);
lean_ctor_set(x_2, 0, x_112);
return x_2;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_2, 0);
x_115 = lean_ctor_get(x_2, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_2);
x_116 = lean_ctor_get(x_65, 6);
lean_inc(x_116);
lean_dec(x_65);
x_117 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_116, x_114);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 1)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_114);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
lean_inc(x_118);
lean_inc(x_115);
x_119 = l_Lake_Package_findTargetModule_x3f(x_115, x_118);
if (lean_obj_tag(x_119) == 1)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_118);
lean_dec(x_115);
lean_dec_ref(x_1);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_122 = 0;
x_123 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_task_pure(x_124);
x_126 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_10);
lean_ctor_set(x_126, 2, x_121);
lean_ctor_set_uint8(x_126, sizeof(void*)*3, x_122);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_8);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_119);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
lean_dec(x_118);
x_129 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_130 = l_Lake_BuildKey_toString(x_1);
x_131 = lean_string_append(x_129, x_130);
lean_dec_ref(x_130);
x_132 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
x_133 = lean_string_append(x_131, x_132);
x_134 = 1;
x_135 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_115, x_134);
x_136 = lean_string_append(x_133, x_135);
lean_dec_ref(x_135);
x_137 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
x_138 = lean_string_append(x_136, x_137);
x_139 = 0;
x_140 = l_Lean_Name_toString(x_128, x_139);
x_141 = lean_string_append(x_138, x_140);
lean_dec_ref(x_140);
x_142 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_143 = lean_string_append(x_141, x_142);
x_144 = 3;
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_144);
x_146 = lean_array_get_size(x_8);
x_147 = lean_array_push(x_8, x_145);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_117);
lean_dec(x_115);
x_149 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_150 = l_Lake_BuildKey_toString(x_1);
x_151 = lean_string_append(x_149, x_150);
lean_dec_ref(x_150);
x_152 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_153 = lean_string_append(x_151, x_152);
x_154 = 1;
x_155 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_114, x_154);
x_156 = lean_string_append(x_153, x_155);
lean_dec_ref(x_155);
x_157 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_158 = lean_string_append(x_156, x_157);
x_159 = 3;
x_160 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_159);
x_161 = lean_array_get_size(x_8);
x_162 = lean_array_push(x_8, x_160);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
case 3:
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_2);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_7, 1);
x_166 = lean_ctor_get(x_2, 0);
x_167 = lean_ctor_get(x_2, 1);
x_168 = lean_ctor_get(x_165, 6);
x_169 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_168, x_166);
if (lean_obj_tag(x_169) == 1)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_166);
lean_dec_ref(x_1);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_170);
x_171 = lean_apply_7(x_3, x_2, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_172 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_173 = l_Lake_BuildKey_toString(x_1);
x_174 = lean_string_append(x_172, x_173);
lean_dec_ref(x_173);
x_175 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_176 = lean_string_append(x_174, x_175);
x_177 = 1;
x_178 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_166, x_177);
x_179 = lean_string_append(x_176, x_178);
lean_dec_ref(x_178);
x_180 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_181 = lean_string_append(x_179, x_180);
x_182 = 3;
x_183 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_182);
x_184 = lean_array_get_size(x_8);
x_185 = lean_array_push(x_8, x_183);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_185);
lean_ctor_set(x_2, 0, x_184);
return x_2;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_7, 1);
x_187 = lean_ctor_get(x_2, 0);
x_188 = lean_ctor_get(x_2, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_2);
x_189 = lean_ctor_get(x_186, 6);
x_190 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_189, x_187);
if (lean_obj_tag(x_190) == 1)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_187);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_188);
x_193 = lean_apply_7(x_3, x_192, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_190);
lean_dec(x_188);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_194 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_195 = l_Lake_BuildKey_toString(x_1);
x_196 = lean_string_append(x_194, x_195);
lean_dec_ref(x_195);
x_197 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_198 = lean_string_append(x_196, x_197);
x_199 = 1;
x_200 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_187, x_199);
x_201 = lean_string_append(x_198, x_200);
lean_dec_ref(x_200);
x_202 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_203 = lean_string_append(x_201, x_202);
x_204 = 3;
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_204);
x_206 = lean_array_get_size(x_8);
x_207 = lean_array_push(x_8, x_205);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
default: 
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_2, 0);
x_210 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_209);
lean_inc_ref(x_1);
x_211 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_1, x_209, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
x_215 = lean_ctor_get(x_213, 1);
x_216 = l_Lean_Name_isAnonymous(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_inc(x_210);
lean_inc_ref(x_209);
lean_dec_ref(x_2);
x_217 = lean_ctor_get(x_7, 1);
x_218 = l_Lake_Workspace_findFacetConfig_x3f(x_210, x_217);
if (lean_obj_tag(x_218) == 1)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec_ref(x_1);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = lean_ctor_get(x_219, 2);
lean_inc(x_220);
lean_dec(x_219);
lean_inc(x_215);
x_221 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed), 11, 3);
lean_closure_set(x_221, 0, x_209);
lean_closure_set(x_221, 1, x_215);
lean_closure_set(x_221, 2, x_210);
x_222 = lean_unsigned_to_nat(0u);
x_223 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3;
x_224 = l_Lake_Job_bindM___redArg(x_220, x_213, x_221, x_222, x_216, x_3, x_4, x_5, x_6, x_7, x_223);
lean_ctor_set(x_211, 0, x_224);
return x_211;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_218);
lean_dec(x_213);
lean_dec_ref(x_209);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_225 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_226 = l_Lake_BuildKey_toString(x_1);
x_227 = lean_string_append(x_225, x_226);
lean_dec_ref(x_226);
x_228 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
x_229 = lean_string_append(x_227, x_228);
x_230 = 1;
x_231 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_210, x_230);
x_232 = lean_string_append(x_229, x_231);
lean_dec_ref(x_231);
x_233 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_234 = lean_string_append(x_232, x_233);
x_235 = 3;
x_236 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set_uint8(x_236, sizeof(void*)*1, x_235);
x_237 = lean_array_get_size(x_214);
x_238 = lean_array_push(x_214, x_236);
lean_ctor_set_tag(x_211, 1);
lean_ctor_set(x_211, 1, x_238);
lean_ctor_set(x_211, 0, x_237);
return x_211;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_213);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_239 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_240 = l_Lake_BuildKey_toString(x_2);
x_241 = lean_string_append(x_239, x_240);
lean_dec_ref(x_240);
x_242 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
x_243 = lean_string_append(x_241, x_242);
x_244 = 3;
x_245 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*1, x_244);
x_246 = lean_array_get_size(x_214);
x_247 = lean_array_push(x_214, x_245);
lean_ctor_set_tag(x_211, 1);
lean_ctor_set(x_211, 1, x_247);
lean_ctor_set(x_211, 0, x_246);
return x_211;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_248 = lean_ctor_get(x_211, 0);
x_249 = lean_ctor_get(x_211, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_211);
x_250 = lean_ctor_get(x_248, 1);
x_251 = l_Lean_Name_isAnonymous(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
lean_inc(x_210);
lean_inc_ref(x_209);
lean_dec_ref(x_2);
x_252 = lean_ctor_get(x_7, 1);
x_253 = l_Lake_Workspace_findFacetConfig_x3f(x_210, x_252);
if (lean_obj_tag(x_253) == 1)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec_ref(x_1);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_ctor_get(x_254, 2);
lean_inc(x_255);
lean_dec(x_254);
lean_inc(x_250);
x_256 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed), 11, 3);
lean_closure_set(x_256, 0, x_209);
lean_closure_set(x_256, 1, x_250);
lean_closure_set(x_256, 2, x_210);
x_257 = lean_unsigned_to_nat(0u);
x_258 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3;
x_259 = l_Lake_Job_bindM___redArg(x_255, x_248, x_256, x_257, x_251, x_3, x_4, x_5, x_6, x_7, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_249);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_253);
lean_dec(x_248);
lean_dec_ref(x_209);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_261 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_262 = l_Lake_BuildKey_toString(x_1);
x_263 = lean_string_append(x_261, x_262);
lean_dec_ref(x_262);
x_264 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
x_265 = lean_string_append(x_263, x_264);
x_266 = 1;
x_267 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_210, x_266);
x_268 = lean_string_append(x_265, x_267);
lean_dec_ref(x_267);
x_269 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_270 = lean_string_append(x_268, x_269);
x_271 = 3;
x_272 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set_uint8(x_272, sizeof(void*)*1, x_271);
x_273 = lean_array_get_size(x_249);
x_274 = lean_array_push(x_249, x_272);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_248);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_276 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_277 = l_Lake_BuildKey_toString(x_2);
x_278 = lean_string_append(x_276, x_277);
lean_dec_ref(x_277);
x_279 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
x_280 = lean_string_append(x_278, x_279);
x_281 = 3;
x_282 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set_uint8(x_282, sizeof(void*)*1, x_281);
x_283 = lean_array_get_size(x_249);
x_284 = lean_array_push(x_249, x_282);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
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
return x_211;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_33; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_13, 1);
x_35 = lean_ctor_get(x_13, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_name_eq(x_36, x_1);
if (x_37 == 0)
{
uint8_t x_38; 
lean_inc(x_36);
lean_free_object(x_13);
lean_dec(x_34);
x_38 = l_Lean_Name_isAnonymous(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_40 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_36, x_11);
x_41 = lean_string_append(x_39, x_40);
lean_dec_ref(x_40);
x_42 = lean_string_append(x_41, x_39);
x_16 = x_42;
goto block_32;
}
else
{
lean_object* x_43; 
lean_dec(x_36);
x_43 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__3));
x_16 = x_43;
goto block_32;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec(x_1);
lean_ctor_set(x_13, 1, x_14);
lean_ctor_set(x_13, 0, x_34);
return x_13;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = lean_ctor_get(x_44, 1);
x_46 = lean_name_eq(x_45, x_1);
if (x_46 == 0)
{
uint8_t x_47; 
lean_inc(x_45);
lean_dec(x_44);
x_47 = l_Lean_Name_isAnonymous(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_49 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_45, x_11);
x_50 = lean_string_append(x_48, x_49);
lean_dec_ref(x_49);
x_51 = lean_string_append(x_50, x_48);
x_16 = x_51;
goto block_32;
}
else
{
lean_object* x_52; 
lean_dec(x_45);
x_52 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__3));
x_16 = x_52;
goto block_32;
}
}
else
{
lean_object* x_53; 
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_14);
return x_53;
}
}
block_32:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__0));
x_18 = l_Lake_PartialBuildKey_toString(x_3);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__1));
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_11);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Lake_Target_fetchIn___redArg___closed__2));
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_16);
lean_dec_ref(x_16);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_14);
x_30 = lean_array_push(x_14, x_28);
if (lean_is_scalar(x_15)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_15;
 lean_ctor_set_tag(x_31, 1);
}
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
static lean_object* _init_l_Lake_TargetArray_fetchIn___redArg___closed__0() {
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
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lake_TargetArray_fetchIn___redArg___closed__0;
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 2);
lean_dec(x_21);
x_22 = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_inc(x_16);
lean_inc(x_18);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_16);
lean_inc(x_16);
lean_inc(x_18);
x_24 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_24, 0, x_18);
lean_closure_set(x_24, 1, x_16);
lean_inc_ref(x_23);
lean_inc(x_18);
x_25 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_25, 0, x_18);
lean_closure_set(x_25, 1, x_23);
lean_inc(x_18);
lean_inc_ref(x_17);
x_26 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_26, 0, x_17);
lean_closure_set(x_26, 1, x_18);
lean_closure_set(x_26, 2, x_16);
x_27 = l_Lake_EStateT_instFunctor___redArg(x_17);
x_28 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_28, 0, x_18);
lean_ctor_set(x_14, 4, x_24);
lean_ctor_set(x_14, 3, x_25);
lean_ctor_set(x_14, 2, x_26);
lean_ctor_set(x_14, 1, x_28);
lean_ctor_set(x_14, 0, x_27);
lean_ctor_set(x_12, 1, x_23);
x_29 = l_ReaderT_instMonad___redArg(x_12);
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = l_ReaderT_instMonad___redArg(x_31);
x_33 = l_Lake_EquipT_instMonad___redArg(x_32);
x_34 = lean_array_size(x_3);
x_35 = 0;
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_33, x_22, x_34, x_35, x_3);
x_37 = lean_apply_7(x_36, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lake_Job_collectArray___redArg(x_39, x_4);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = l_Lake_Job_collectArray___redArg(x_41, x_4);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec_ref(x_4);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_49 = lean_ctor_get(x_12, 1);
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_14);
x_52 = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_2);
lean_inc(x_49);
lean_inc(x_51);
x_53 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_53, 0, x_51);
lean_closure_set(x_53, 1, x_49);
lean_inc(x_49);
lean_inc(x_51);
x_54 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_54, 0, x_51);
lean_closure_set(x_54, 1, x_49);
lean_inc_ref(x_53);
lean_inc(x_51);
x_55 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_55, 0, x_51);
lean_closure_set(x_55, 1, x_53);
lean_inc(x_51);
lean_inc_ref(x_50);
x_56 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_56, 0, x_50);
lean_closure_set(x_56, 1, x_51);
lean_closure_set(x_56, 2, x_49);
x_57 = l_Lake_EStateT_instFunctor___redArg(x_50);
x_58 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_58, 0, x_51);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_54);
lean_ctor_set(x_12, 1, x_53);
lean_ctor_set(x_12, 0, x_59);
x_60 = l_ReaderT_instMonad___redArg(x_12);
x_61 = l_ReaderT_instMonad___redArg(x_60);
x_62 = l_ReaderT_instMonad___redArg(x_61);
x_63 = l_ReaderT_instMonad___redArg(x_62);
x_64 = l_Lake_EquipT_instMonad___redArg(x_63);
x_65 = lean_array_size(x_3);
x_66 = 0;
x_67 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_64, x_52, x_65, x_66, x_3);
x_68 = lean_apply_7(x_67, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_Lake_Job_collectArray___redArg(x_69, x_4);
lean_dec(x_69);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_4);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; lean_object* x_100; 
x_78 = lean_ctor_get(x_12, 0);
x_79 = lean_ctor_get(x_12, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_12);
x_80 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed), 10, 2);
lean_closure_set(x_83, 0, x_1);
lean_closure_set(x_83, 1, x_2);
lean_inc(x_79);
lean_inc(x_81);
x_84 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_84, 0, x_81);
lean_closure_set(x_84, 1, x_79);
lean_inc(x_79);
lean_inc(x_81);
x_85 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_85, 0, x_81);
lean_closure_set(x_85, 1, x_79);
lean_inc_ref(x_84);
lean_inc(x_81);
x_86 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_86, 0, x_81);
lean_closure_set(x_86, 1, x_84);
lean_inc(x_81);
lean_inc_ref(x_80);
x_87 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_87, 0, x_80);
lean_closure_set(x_87, 1, x_81);
lean_closure_set(x_87, 2, x_79);
x_88 = l_Lake_EStateT_instFunctor___redArg(x_80);
x_89 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_89, 0, x_81);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_87);
lean_ctor_set(x_90, 3, x_86);
lean_ctor_set(x_90, 4, x_85);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_84);
x_92 = l_ReaderT_instMonad___redArg(x_91);
x_93 = l_ReaderT_instMonad___redArg(x_92);
x_94 = l_ReaderT_instMonad___redArg(x_93);
x_95 = l_ReaderT_instMonad___redArg(x_94);
x_96 = l_Lake_EquipT_instMonad___redArg(x_95);
x_97 = lean_array_size(x_3);
x_98 = 0;
x_99 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_96, x_83, x_97, x_98, x_3);
x_100 = lean_apply_7(x_99, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l_Lake_Job_collectArray___redArg(x_101, x_4);
lean_dec(x_101);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_4);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_108 = x_100;
} else {
 lean_dec_ref(x_100);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
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
l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0 = _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0();
lean_mark_persistent(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0);
l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3 = _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3();
lean_mark_persistent(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4 = _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4();
lean_mark_persistent(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
l_Lake_TargetArray_fetchIn___redArg___closed__0 = _init_l_Lake_TargetArray_fetchIn___redArg___closed__0();
lean_mark_persistent(l_Lake_TargetArray_fetchIn___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
