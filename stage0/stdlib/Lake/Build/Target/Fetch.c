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
lean_object* x_7; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_24; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec_ref(x_4);
x_26 = lean_ctor_get(x_25, 6);
lean_inc(x_26);
lean_dec(x_25);
x_27 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(x_3);
x_28 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_27, x_26, x_3);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_28);
x_31 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_32 = l_Lake_PartialBuildKey_toString(x_2);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_35 = lean_string_append(x_33, x_34);
x_36 = 1;
x_37 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_36);
x_38 = lean_string_append(x_35, x_37);
lean_dec_ref(x_37);
x_39 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_40 = lean_string_append(x_38, x_39);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_5);
x_44 = lean_array_push(x_5, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_64; 
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_dec_ref(x_4);
x_47 = lean_ctor_get(x_46, 5);
lean_inc_ref(x_47);
lean_dec(x_46);
x_48 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13));
x_49 = lean_box(0);
x_50 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
lean_inc(x_3);
x_51 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_51, 0, x_3);
lean_closure_set(x_51, 1, x_50);
lean_closure_set(x_51, 2, x_49);
x_52 = lean_array_size(x_47);
x_53 = 0;
x_54 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_48, x_47, x_51, x_52, x_53, x_50);
x_55 = lean_ctor_get(x_54, 0);
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_54, 1);
lean_dec(x_65);
x_56 = x_54;
x_57 = x_64;
goto block_63;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_64;
goto block_63;
}
block_63:
{
if (lean_obj_tag(x_55) == 0)
{
lean_del_object(x_56);
x_7 = x_5;
goto block_23;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec_ref(x_55);
if (lean_obj_tag(x_58) == 1)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
if (x_57 == 0)
{
lean_ctor_set(x_56, 1, x_5);
lean_ctor_set(x_56, 0, x_59);
x_60 = x_56;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_5);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
else
{
lean_dec(x_58);
lean_del_object(x_56);
x_7 = x_5;
goto block_23;
}
}
}
}
}
block_23:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_9 = l_Lake_PartialBuildKey_toString(x_2);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_12 = lean_string_append(x_10, x_11);
x_13 = 1;
x_14 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_17 = lean_string_append(x_15, x_16);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_7);
x_21 = lean_array_push(x_7, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
lean_object* x_11; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_28; 
lean_dec_ref(x_8);
lean_dec_ref(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec_ref(x_8);
x_30 = lean_ctor_get(x_29, 6);
lean_inc(x_30);
lean_dec(x_29);
x_31 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3));
lean_inc_ref(x_3);
x_32 = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(x_31, x_30, x_3);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
x_35 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_36 = l_Lake_PartialBuildKey_toString(x_2);
x_37 = lean_string_append(x_35, x_36);
lean_dec_ref(x_36);
x_38 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_39 = lean_string_append(x_37, x_38);
x_40 = 1;
x_41 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_40);
x_42 = lean_string_append(x_39, x_41);
lean_dec_ref(x_41);
x_43 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_44 = lean_string_append(x_42, x_43);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_get_size(x_9);
x_48 = lean_array_push(x_9, x_46);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
default: 
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_68; 
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_dec_ref(x_8);
x_51 = lean_ctor_get(x_50, 5);
lean_inc_ref(x_51);
lean_dec(x_50);
x_52 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13));
x_53 = lean_box(0);
x_54 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
lean_inc(x_3);
x_55 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 6, 3);
lean_closure_set(x_55, 0, x_3);
lean_closure_set(x_55, 1, x_54);
lean_closure_set(x_55, 2, x_53);
x_56 = lean_array_size(x_51);
x_57 = 0;
x_58 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_52, x_51, x_55, x_56, x_57, x_54);
x_59 = lean_ctor_get(x_58, 0);
x_68 = !lean_is_exclusive(x_58);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_58, 1);
lean_dec(x_69);
x_60 = x_58;
x_61 = x_68;
goto block_67;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_68;
goto block_67;
}
block_67:
{
if (lean_obj_tag(x_59) == 0)
{
lean_del_object(x_60);
x_11 = x_9;
goto block_27;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec_ref(x_59);
if (lean_obj_tag(x_62) == 1)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
if (x_61 == 0)
{
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 0, x_63);
x_64 = x_60;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_9);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
else
{
lean_dec(x_62);
lean_del_object(x_60);
x_11 = x_9;
goto block_27;
}
}
}
}
}
block_27:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_13 = l_Lake_PartialBuildKey_toString(x_2);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = 1;
x_18 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_21 = lean_string_append(x_19, x_20);
x_22 = 3;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_array_get_size(x_11);
x_25 = lean_array_push(x_11, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
lean_object* x_12; lean_object* x_13; lean_object* x_16; lean_object* x_17; lean_object* x_20; lean_object* x_21; lean_object* x_24; 
x_24 = l_Lake_instDataKindModule;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec_ref(x_3);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec_ref(x_9);
lean_inc(x_25);
x_27 = l_Lake_Workspace_findModule_x3f(x_25, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_29, 0);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
x_33 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_34 = 0;
x_35 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_task_pure(x_36);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_27);
x_41 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_42 = l_Lake_PartialBuildKey_toString(x_2);
x_43 = lean_string_append(x_41, x_42);
lean_dec_ref(x_42);
x_44 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5));
x_45 = lean_string_append(x_43, x_44);
x_46 = 1;
x_47 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_25, x_46);
x_48 = lean_string_append(x_45, x_47);
lean_dec_ref(x_47);
x_49 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_50 = lean_string_append(x_48, x_49);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_get_size(x_10);
x_54 = lean_array_push(x_10, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
case 1:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_119; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_56 = lean_ctor_get(x_3, 0);
x_119 = !lean_is_exclusive(x_3);
if (x_119 == 0)
{
x_57 = x_3;
x_58 = x_119;
goto block_118;
}
else
{
lean_inc(x_56);
lean_dec(x_3);
x_57 = lean_box(0);
x_58 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_59; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Lake_instDataKindPackage;
switch (lean_obj_tag(x_56)) {
case 0:
{
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_76 = x_1;
x_77 = x_10;
goto block_90;
}
case 2:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_9, 1);
lean_inc(x_91);
lean_dec_ref(x_9);
x_92 = lean_ctor_get(x_91, 6);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_92, x_56);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_94; 
lean_dec_ref(x_56);
lean_dec_ref(x_2);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_76 = x_94;
x_77 = x_10;
goto block_90;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_93);
lean_del_object(x_57);
x_95 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_96 = l_Lake_PartialBuildKey_toString(x_2);
x_97 = lean_string_append(x_95, x_96);
lean_dec_ref(x_96);
x_98 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_99 = lean_string_append(x_97, x_98);
x_100 = 1;
x_101 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_56, x_100);
x_102 = lean_string_append(x_99, x_101);
lean_dec_ref(x_101);
x_103 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_104 = lean_string_append(x_102, x_103);
x_105 = 3;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
x_107 = lean_array_get_size(x_10);
x_108 = lean_array_push(x_10, x_106);
x_20 = x_107;
x_21 = x_108;
goto block_23;
}
}
default: 
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_1);
x_109 = lean_ctor_get(x_9, 1);
lean_inc(x_109);
lean_dec_ref(x_9);
x_110 = lean_ctor_get(x_109, 5);
lean_inc_ref(x_110);
lean_dec(x_109);
x_111 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_112 = lean_array_size(x_110);
x_113 = 0;
x_114 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_56, x_110, x_112, x_113, x_111);
lean_dec_ref(x_110);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_del_object(x_57);
x_59 = x_10;
goto block_74;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; 
lean_dec(x_56);
lean_dec_ref(x_2);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_76 = x_117;
x_77 = x_10;
goto block_90;
}
else
{
lean_dec(x_116);
lean_del_object(x_57);
x_59 = x_10;
goto block_74;
}
}
}
}
block_74:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_60 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_61 = l_Lake_PartialBuildKey_toString(x_2);
x_62 = lean_string_append(x_60, x_61);
lean_dec_ref(x_61);
x_63 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_64 = lean_string_append(x_62, x_63);
x_65 = 1;
x_66 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_56, x_65);
x_67 = lean_string_append(x_64, x_66);
lean_dec_ref(x_66);
x_68 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_69 = lean_string_append(x_67, x_68);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_59);
x_73 = lean_array_push(x_59, x_71);
x_20 = x_72;
x_21 = x_73;
goto block_23;
}
block_90:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 2);
lean_inc(x_78);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_78);
x_79 = x_57;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_78);
x_79 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_81 = 0;
x_82 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_task_pure(x_83);
x_85 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_75);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set_uint8(x_85, sizeof(void*)*3, x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
return x_87;
}
}
}
}
case 2:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_206; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_120 = lean_ctor_get(x_3, 0);
x_121 = lean_ctor_get(x_3, 1);
x_206 = !lean_is_exclusive(x_3);
if (x_206 == 0)
{
x_122 = x_3;
x_123 = x_206;
goto block_205;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_3);
x_122 = lean_box(0);
x_123 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_124; lean_object* x_125; lean_object* x_162; 
switch (lean_obj_tag(x_120)) {
case 0:
{
lean_dec_ref(x_9);
x_124 = x_1;
x_125 = x_10;
goto block_161;
}
case 2:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_9, 1);
lean_inc(x_178);
lean_dec_ref(x_9);
x_179 = lean_ctor_get(x_178, 6);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_179, x_120);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 1)
{
lean_object* x_181; 
lean_dec_ref(x_120);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_124 = x_181;
x_125 = x_10;
goto block_161;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_180);
lean_del_object(x_122);
lean_dec(x_121);
x_182 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_183 = l_Lake_PartialBuildKey_toString(x_2);
x_184 = lean_string_append(x_182, x_183);
lean_dec_ref(x_183);
x_185 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_186 = lean_string_append(x_184, x_185);
x_187 = 1;
x_188 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_120, x_187);
x_189 = lean_string_append(x_186, x_188);
lean_dec_ref(x_188);
x_190 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_191 = lean_string_append(x_189, x_190);
x_192 = 3;
x_193 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_192);
x_194 = lean_array_get_size(x_10);
x_195 = lean_array_push(x_10, x_193);
x_16 = x_194;
x_17 = x_195;
goto block_19;
}
}
default: 
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; size_t x_199; size_t x_200; lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_1);
x_196 = lean_ctor_get(x_9, 1);
lean_inc(x_196);
lean_dec_ref(x_9);
x_197 = lean_ctor_get(x_196, 5);
lean_inc_ref(x_197);
lean_dec(x_196);
x_198 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_199 = lean_array_size(x_197);
x_200 = 0;
x_201 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_120, x_197, x_199, x_200, x_198);
lean_dec_ref(x_197);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_del_object(x_122);
lean_dec(x_121);
x_162 = x_10;
goto block_177;
}
else
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
if (lean_obj_tag(x_203) == 1)
{
lean_object* x_204; 
lean_dec(x_120);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_124 = x_204;
x_125 = x_10;
goto block_161;
}
else
{
lean_dec(x_203);
lean_del_object(x_122);
lean_dec(x_121);
x_162 = x_10;
goto block_177;
}
}
}
}
block_161:
{
lean_object* x_126; 
lean_inc_ref(x_124);
lean_inc(x_121);
x_126 = l_Lake_Package_findTargetModule_x3f(x_121, x_124);
if (lean_obj_tag(x_126) == 1)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_2);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_ctor_get(x_124, 2);
lean_inc(x_128);
lean_dec_ref(x_124);
if (x_123 == 0)
{
lean_ctor_set(x_122, 0, x_128);
x_129 = x_122;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_128);
lean_ctor_set(x_139, 1, x_121);
x_129 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_130 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1));
x_131 = 0;
x_132 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_task_pure(x_133);
x_135 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_24);
lean_ctor_set(x_135, 2, x_130);
lean_ctor_set_uint8(x_135, sizeof(void*)*3, x_131);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_125);
return x_137;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_126);
lean_del_object(x_122);
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
lean_dec_ref(x_124);
x_141 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_142 = l_Lake_PartialBuildKey_toString(x_2);
x_143 = lean_string_append(x_141, x_142);
lean_dec_ref(x_142);
x_144 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6));
x_145 = lean_string_append(x_143, x_144);
x_146 = 1;
x_147 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_121, x_146);
x_148 = lean_string_append(x_145, x_147);
lean_dec_ref(x_147);
x_149 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7));
x_150 = lean_string_append(x_148, x_149);
x_151 = 0;
x_152 = l_Lean_Name_toString(x_140, x_151);
x_153 = lean_string_append(x_150, x_152);
lean_dec_ref(x_152);
x_154 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_155 = lean_string_append(x_153, x_154);
x_156 = 3;
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_156);
x_158 = lean_array_get_size(x_125);
x_159 = lean_array_push(x_125, x_157);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
block_177:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_163 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_164 = l_Lake_PartialBuildKey_toString(x_2);
x_165 = lean_string_append(x_163, x_164);
lean_dec_ref(x_164);
x_166 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_167 = lean_string_append(x_165, x_166);
x_168 = 1;
x_169 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_120, x_168);
x_170 = lean_string_append(x_167, x_169);
lean_dec_ref(x_169);
x_171 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_172 = lean_string_append(x_170, x_171);
x_173 = 3;
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = lean_array_get_size(x_162);
x_176 = lean_array_push(x_162, x_174);
x_16 = x_175;
x_17 = x_176;
goto block_19;
}
}
}
case 3:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_358; 
x_207 = lean_ctor_get(x_3, 0);
x_208 = lean_ctor_get(x_3, 1);
x_358 = !lean_is_exclusive(x_3);
if (x_358 == 0)
{
x_209 = x_3;
x_210 = x_358;
goto block_357;
}
else
{
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_3);
x_209 = lean_box(0);
x_210 = x_358;
goto block_357;
}
block_357:
{
lean_object* x_211; lean_object* x_212; lean_object* x_314; 
switch (lean_obj_tag(x_207)) {
case 0:
{
x_211 = x_1;
x_212 = x_10;
goto block_313;
}
case 2:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec_ref(x_1);
x_330 = lean_ctor_get(x_9, 1);
x_331 = lean_ctor_get(x_330, 6);
x_332 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(x_331, x_207);
if (lean_obj_tag(x_332) == 1)
{
lean_object* x_333; 
lean_dec_ref(x_207);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec_ref(x_332);
x_211 = x_333;
x_212 = x_10;
goto block_313;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_332);
lean_del_object(x_209);
lean_dec(x_208);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_334 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_335 = l_Lake_PartialBuildKey_toString(x_2);
x_336 = lean_string_append(x_334, x_335);
lean_dec_ref(x_335);
x_337 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_338 = lean_string_append(x_336, x_337);
x_339 = 1;
x_340 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_207, x_339);
x_341 = lean_string_append(x_338, x_340);
lean_dec_ref(x_340);
x_342 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_343 = lean_string_append(x_341, x_342);
x_344 = 3;
x_345 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*1, x_344);
x_346 = lean_array_get_size(x_10);
x_347 = lean_array_push(x_10, x_345);
x_12 = x_346;
x_13 = x_347;
goto block_15;
}
}
default: 
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; size_t x_351; size_t x_352; lean_object* x_353; lean_object* x_354; 
lean_dec_ref(x_1);
x_348 = lean_ctor_get(x_9, 1);
x_349 = lean_ctor_get(x_348, 5);
x_350 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14));
x_351 = lean_array_size(x_349);
x_352 = 0;
x_353 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(x_207, x_349, x_351, x_352, x_350);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
lean_dec_ref(x_353);
if (lean_obj_tag(x_354) == 0)
{
lean_del_object(x_209);
lean_dec(x_208);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_314 = x_10;
goto block_329;
}
else
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
lean_dec_ref(x_354);
if (lean_obj_tag(x_355) == 1)
{
lean_object* x_356; 
lean_dec(x_207);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec_ref(x_355);
x_211 = x_356;
x_212 = x_10;
goto block_313;
}
else
{
lean_dec(x_355);
lean_del_object(x_209);
lean_dec(x_208);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_314 = x_10;
goto block_329;
}
}
}
}
block_313:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_211, 1);
x_214 = lean_ctor_get(x_211, 2);
lean_inc(x_208);
lean_inc(x_214);
if (x_210 == 0)
{
lean_ctor_set(x_209, 0, x_214);
x_215 = x_209;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_312, 0, x_214);
lean_ctor_set(x_312, 1, x_208);
x_215 = x_312;
goto block_311;
}
block_311:
{
if (x_4 == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_dec_ref(x_2);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_208);
x_217 = lean_apply_7(x_5, x_216, x_6, x_7, x_8, x_9, x_212, lean_box(0));
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_227; 
x_218 = lean_ctor_get(x_217, 0);
x_219 = lean_ctor_get(x_217, 1);
x_227 = !lean_is_exclusive(x_217);
if (x_227 == 0)
{
x_220 = x_217;
x_221 = x_227;
goto block_226;
}
else
{
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_217);
x_220 = lean_box(0);
x_221 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_215);
lean_ctor_set(x_222, 1, x_218);
if (x_221 == 0)
{
lean_ctor_set(x_220, 0, x_222);
x_223 = x_220;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_219);
x_223 = x_225;
goto block_224;
}
block_224:
{
return x_223;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_236; 
lean_dec_ref(x_215);
x_228 = lean_ctor_get(x_217, 0);
x_229 = lean_ctor_get(x_217, 1);
x_236 = !lean_is_exclusive(x_217);
if (x_236 == 0)
{
x_230 = x_217;
x_231 = x_236;
goto block_235;
}
else
{
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_217);
x_230 = lean_box(0);
x_231 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_232; 
if (x_231 == 0)
{
x_232 = x_230;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_228);
lean_ctor_set(x_234, 1, x_229);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
}
}
}
}
else
{
lean_object* x_237; 
x_237 = l_Lake_Package_findTargetDecl_x3f(x_208, x_211);
if (lean_obj_tag(x_237) == 1)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_294; 
lean_dec_ref(x_2);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
x_239 = lean_ctor_get(x_238, 1);
x_240 = lean_ctor_get(x_238, 2);
x_241 = lean_ctor_get(x_238, 3);
x_294 = !lean_is_exclusive(x_238);
if (x_294 == 0)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_238, 0);
lean_dec(x_295);
x_242 = x_238;
x_243 = x_294;
goto block_293;
}
else
{
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_238);
x_242 = lean_box(0);
x_243 = x_294;
goto block_293;
}
block_293:
{
uint8_t x_244; 
x_244 = l_Lean_Name_isAnonymous(x_240);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_208);
x_245 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9));
lean_inc(x_240);
x_246 = l_Lean_Name_str___override(x_240, x_245);
x_247 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_247, 0, x_211);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_241);
lean_inc(x_246);
lean_inc_ref(x_215);
if (x_243 == 0)
{
lean_ctor_set_tag(x_242, 1);
lean_ctor_set(x_242, 3, x_246);
lean_ctor_set(x_242, 2, x_247);
lean_ctor_set(x_242, 1, x_240);
lean_ctor_set(x_242, 0, x_215);
x_248 = x_242;
goto block_270;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_271, 0, x_215);
lean_ctor_set(x_271, 1, x_240);
lean_ctor_set(x_271, 2, x_247);
lean_ctor_set(x_271, 3, x_246);
x_248 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_249; 
x_249 = lean_apply_7(x_5, x_248, x_6, x_7, x_8, x_9, x_212, lean_box(0));
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_260; 
x_250 = lean_ctor_get(x_249, 0);
x_251 = lean_ctor_get(x_249, 1);
x_260 = !lean_is_exclusive(x_249);
if (x_260 == 0)
{
x_252 = x_249;
x_253 = x_260;
goto block_259;
}
else
{
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_249);
x_252 = lean_box(0);
x_253 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_254, 0, x_215);
lean_ctor_set(x_254, 1, x_246);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_250);
if (x_253 == 0)
{
lean_ctor_set(x_252, 0, x_255);
x_256 = x_252;
goto block_257;
}
else
{
lean_object* x_258; 
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_251);
x_256 = x_258;
goto block_257;
}
block_257:
{
return x_256;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_269; 
lean_dec(x_246);
lean_dec_ref(x_215);
x_261 = lean_ctor_get(x_249, 0);
x_262 = lean_ctor_get(x_249, 1);
x_269 = !lean_is_exclusive(x_249);
if (x_269 == 0)
{
x_263 = x_249;
x_264 = x_269;
goto block_268;
}
else
{
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_249);
x_263 = lean_box(0);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_264 == 0)
{
x_265 = x_263;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_261);
lean_ctor_set(x_267, 1, x_262);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_del_object(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_211);
lean_ctor_set(x_272, 1, x_208);
x_273 = lean_apply_7(x_5, x_272, x_6, x_7, x_8, x_9, x_212, lean_box(0));
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_283; 
x_274 = lean_ctor_get(x_273, 0);
x_275 = lean_ctor_get(x_273, 1);
x_283 = !lean_is_exclusive(x_273);
if (x_283 == 0)
{
x_276 = x_273;
x_277 = x_283;
goto block_282;
}
else
{
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_273);
x_276 = lean_box(0);
x_277 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_215);
lean_ctor_set(x_278, 1, x_274);
if (x_277 == 0)
{
lean_ctor_set(x_276, 0, x_278);
x_279 = x_276;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_275);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_292; 
lean_dec_ref(x_215);
x_284 = lean_ctor_get(x_273, 0);
x_285 = lean_ctor_get(x_273, 1);
x_292 = !lean_is_exclusive(x_273);
if (x_292 == 0)
{
x_286 = x_273;
x_287 = x_292;
goto block_291;
}
else
{
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_273);
x_286 = lean_box(0);
x_287 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_288; 
if (x_287 == 0)
{
x_288 = x_286;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_284);
lean_ctor_set(x_290, 1, x_285);
x_288 = x_290;
goto block_289;
}
block_289:
{
return x_288;
}
}
}
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_inc(x_213);
lean_dec(x_237);
lean_dec_ref(x_215);
lean_dec_ref(x_211);
lean_dec(x_208);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_296 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_297 = l_Lake_PartialBuildKey_toString(x_2);
x_298 = lean_string_append(x_296, x_297);
lean_dec_ref(x_297);
x_299 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10));
x_300 = lean_string_append(x_298, x_299);
x_301 = 0;
x_302 = l_Lean_Name_toString(x_213, x_301);
x_303 = lean_string_append(x_300, x_302);
lean_dec_ref(x_302);
x_304 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_305 = lean_string_append(x_303, x_304);
x_306 = 3;
x_307 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set_uint8(x_307, sizeof(void*)*1, x_306);
x_308 = lean_array_get_size(x_212);
x_309 = lean_array_push(x_212, x_307);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
block_329:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_315 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_316 = l_Lake_PartialBuildKey_toString(x_2);
x_317 = lean_string_append(x_315, x_316);
lean_dec_ref(x_316);
x_318 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1));
x_319 = lean_string_append(x_317, x_318);
x_320 = 1;
x_321 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_207, x_320);
x_322 = lean_string_append(x_319, x_321);
lean_dec_ref(x_321);
x_323 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2));
x_324 = lean_string_append(x_322, x_323);
x_325 = 3;
x_326 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set_uint8(x_326, sizeof(void*)*1, x_325);
x_327 = lean_array_get_size(x_314);
x_328 = lean_array_push(x_314, x_326);
x_12 = x_327;
x_13 = x_328;
goto block_15;
}
}
}
default: 
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_430; 
x_359 = lean_ctor_get(x_3, 0);
x_360 = lean_ctor_get(x_3, 1);
x_430 = !lean_is_exclusive(x_3);
if (x_430 == 0)
{
x_361 = x_3;
x_362 = x_430;
goto block_429;
}
else
{
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_3);
x_361 = lean_box(0);
x_362 = x_430;
goto block_429;
}
block_429:
{
uint8_t x_363; lean_object* x_364; 
x_363 = 0;
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_359);
lean_inc_ref(x_2);
x_364 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_359, x_363, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; uint8_t x_427; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_365, 1);
x_427 = !lean_is_exclusive(x_365);
if (x_427 == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_365, 0);
lean_dec(x_428);
x_367 = x_365;
x_368 = x_427;
goto block_426;
}
else
{
lean_inc(x_366);
lean_dec(x_365);
x_367 = lean_box(0);
x_368 = x_427;
goto block_426;
}
block_426:
{
lean_object* x_369; lean_object* x_370; uint8_t x_371; uint8_t x_424; 
x_369 = lean_ctor_get(x_364, 1);
x_424 = !lean_is_exclusive(x_364);
if (x_424 == 0)
{
lean_object* x_425; 
x_425 = lean_ctor_get(x_364, 0);
lean_dec(x_425);
x_370 = x_364;
x_371 = x_424;
goto block_423;
}
else
{
lean_inc(x_369);
lean_dec(x_364);
x_370 = lean_box(0);
x_371 = x_424;
goto block_423;
}
block_423:
{
lean_object* x_372; lean_object* x_373; uint8_t x_410; 
x_372 = lean_ctor_get(x_366, 1);
x_410 = l_Lean_Name_isAnonymous(x_372);
if (x_410 == 0)
{
uint8_t x_411; 
x_411 = l_Lean_Name_isAnonymous(x_360);
if (x_411 == 0)
{
x_373 = x_360;
goto block_409;
}
else
{
lean_object* x_412; 
lean_dec(x_360);
x_412 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12));
x_373 = x_412;
goto block_409;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_del_object(x_370);
lean_del_object(x_367);
lean_dec(x_366);
lean_del_object(x_361);
lean_dec(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_413 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_414 = l_Lake_PartialBuildKey_toString(x_2);
x_415 = lean_string_append(x_413, x_414);
lean_dec_ref(x_414);
x_416 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13));
x_417 = lean_string_append(x_415, x_416);
x_418 = 3;
x_419 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set_uint8(x_419, sizeof(void*)*1, x_418);
x_420 = lean_array_get_size(x_369);
x_421 = lean_array_push(x_369, x_419);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
block_409:
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_9, 1);
lean_inc(x_372);
x_375 = l_Lean_Name_append(x_372, x_373);
x_376 = l_Lake_Workspace_findFacetConfig_x3f(x_375, x_374);
if (lean_obj_tag(x_376) == 1)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec_ref(x_2);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
lean_dec_ref(x_376);
x_378 = lean_ctor_get(x_377, 2);
lean_inc(x_378);
lean_dec(x_377);
lean_inc(x_375);
lean_inc(x_372);
lean_inc_ref(x_359);
x_379 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 11, 3);
lean_closure_set(x_379, 0, x_359);
lean_closure_set(x_379, 1, x_372);
lean_closure_set(x_379, 2, x_375);
x_380 = lean_unsigned_to_nat(0u);
x_381 = lean_obj_once(&l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3, &l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once, _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
x_382 = l_Lake_Job_bindM___redArg(x_378, x_366, x_379, x_380, x_363, x_5, x_6, x_7, x_8, x_9, x_381);
if (x_362 == 0)
{
lean_ctor_set(x_361, 1, x_375);
x_383 = x_361;
goto block_390;
}
else
{
lean_object* x_391; 
x_391 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_391, 0, x_359);
lean_ctor_set(x_391, 1, x_375);
x_383 = x_391;
goto block_390;
}
block_390:
{
lean_object* x_384; 
if (x_368 == 0)
{
lean_ctor_set(x_367, 1, x_382);
lean_ctor_set(x_367, 0, x_383);
x_384 = x_367;
goto block_388;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_383);
lean_ctor_set(x_389, 1, x_382);
x_384 = x_389;
goto block_388;
}
block_388:
{
lean_object* x_385; 
if (x_371 == 0)
{
lean_ctor_set(x_370, 0, x_384);
x_385 = x_370;
goto block_386;
}
else
{
lean_object* x_387; 
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_369);
x_385 = x_387;
goto block_386;
}
block_386:
{
return x_385;
}
}
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_376);
lean_del_object(x_367);
lean_dec(x_366);
lean_del_object(x_361);
lean_dec_ref(x_359);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_392 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0));
x_393 = l_Lake_PartialBuildKey_toString(x_2);
x_394 = lean_string_append(x_392, x_393);
lean_dec_ref(x_393);
x_395 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11));
x_396 = lean_string_append(x_394, x_395);
x_397 = 1;
x_398 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_375, x_397);
x_399 = lean_string_append(x_396, x_398);
lean_dec_ref(x_398);
x_400 = ((lean_object*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8));
x_401 = lean_string_append(x_399, x_400);
x_402 = 3;
x_403 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set_uint8(x_403, sizeof(void*)*1, x_402);
x_404 = lean_array_get_size(x_369);
x_405 = lean_array_push(x_369, x_403);
if (x_371 == 0)
{
lean_ctor_set_tag(x_370, 1);
lean_ctor_set(x_370, 1, x_405);
lean_ctor_set(x_370, 0, x_404);
x_406 = x_370;
goto block_407;
}
else
{
lean_object* x_408; 
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_404);
lean_ctor_set(x_408, 1, x_405);
x_406 = x_408;
goto block_407;
}
block_407:
{
return x_406;
}
}
}
}
}
}
else
{
lean_del_object(x_361);
lean_dec(x_360);
lean_dec_ref(x_359);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_364;
}
}
}
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
block_23:
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
