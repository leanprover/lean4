// Lean compiler output
// Module: Lake.Toml.Data.Dict
// Imports: public import Lean.Data.NameMap.Basic import Init.Data.Nat.Fold
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static const lean_array_object l_Lake_Toml_instInhabitedRBDict_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_instInhabitedRBDict_default___closed__0 = (const lean_object*)&l_Lake_Toml_instInhabitedRBDict_default___closed__0_value;
static const lean_ctor_object l_Lake_Toml_instInhabitedRBDict_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_instInhabitedRBDict_default___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_instInhabitedRBDict_default___closed__1 = (const lean_object*)&l_Lake_Toml_instInhabitedRBDict_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Toml_RBDict_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_RBDict_empty___closed__0 = (const lean_object*)&l_Lake_Toml_RBDict_empty___closed__0_value;
static const lean_ctor_object l_Lake_Toml_RBDict_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_RBDict_empty___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_RBDict_empty___closed__1 = (const lean_object*)&l_Lake_Toml_RBDict_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_RBDict_map___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__0_value;
static const lean_closure_object l_Lake_Toml_RBDict_map___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__1_value;
static const lean_closure_object l_Lake_Toml_RBDict_map___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__2 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__2_value;
static const lean_closure_object l_Lake_Toml_RBDict_map___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__3 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__3_value;
static const lean_closure_object l_Lake_Toml_RBDict_map___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__4 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__4_value;
static const lean_closure_object l_Lake_Toml_RBDict_map___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__5 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__5_value;
static const lean_closure_object l_Lake_Toml_RBDict_map___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__6 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__6_value;
static const lean_ctor_object l_Lake_Toml_RBDict_map___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__0_value),((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__1_value)}};
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__7 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__7_value;
static const lean_ctor_object l_Lake_Toml_RBDict_map___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__7_value),((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__2_value),((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__3_value),((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__4_value),((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__5_value)}};
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__8 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__8_value;
static const lean_ctor_object l_Lake_Toml_RBDict_map___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__8_value),((lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__6_value)}};
static const lean_object* l_Lake_Toml_RBDict_map___redArg___closed__9 = (const lean_object*)&l_Lake_Toml_RBDict_map___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_cmp_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = ((lean_object*)(l_Lake_Toml_instInhabitedRBDict_default___closed__1));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_cmp_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lake_Toml_instInhabitedRBDict_default(v_00_u03b1_10_, v_00_u03b2_11_, v_cmp_12_);
lean_dec_ref(v_cmp_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg(lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lake_Toml_instInhabitedRBDict_default(lean_box(0), lean_box(0), v_a_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg___boxed(lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lake_Toml_instInhabitedRBDict___redArg(v_a_16_);
lean_dec_ref(v_a_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict(lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lake_Toml_instInhabitedRBDict_default(lean_box(0), lean_box(0), v_a_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___boxed(lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_Toml_instInhabitedRBDict(v_a_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_a_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_cmp_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = ((lean_object*)(l_Lake_Toml_RBDict_empty___closed__1));
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___boxed(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_cmp_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_Toml_RBDict_empty(v_00_u03b1_35_, v_00_u03b2_36_, v_cmp_37_);
lean_dec_ref(v_cmp_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg(lean_object* v_cmp_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg___boxed(lean_object* v_cmp_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lake_Toml_RBDict_instEmptyCollection___redArg(v_cmp_41_);
lean_dec_ref(v_cmp_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_cmp_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___boxed(lean_object* v_00_u03b1_47_, lean_object* v_00_u03b2_48_, lean_object* v_cmp_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_Toml_RBDict_instEmptyCollection(v_00_u03b1_47_, v_00_u03b2_48_, v_cmp_49_);
lean_dec_ref(v_cmp_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg(lean_object* v_capacity_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_mk_empty_array_with_capacity(v_capacity_51_);
v___x_53_ = lean_box(1);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg___boxed(lean_object* v_capacity_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_55_);
lean_dec(v_capacity_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_cmp_59_, lean_object* v_capacity_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___boxed(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_cmp_64_, lean_object* v_capacity_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lake_Toml_RBDict_mkEmpty(v_00_u03b1_62_, v_00_u03b2_63_, v_cmp_64_, v_capacity_65_);
lean_dec(v_capacity_65_);
lean_dec_ref(v_cmp_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(lean_object* v_cmp_67_, lean_object* v_k_68_, lean_object* v_v_69_, lean_object* v_t_70_){
_start:
{
if (lean_obj_tag(v_t_70_) == 0)
{
lean_object* v_size_71_; lean_object* v_k_72_; lean_object* v_v_73_; lean_object* v_l_74_; lean_object* v_r_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_356_; 
v_size_71_ = lean_ctor_get(v_t_70_, 0);
v_k_72_ = lean_ctor_get(v_t_70_, 1);
v_v_73_ = lean_ctor_get(v_t_70_, 2);
v_l_74_ = lean_ctor_get(v_t_70_, 3);
v_r_75_ = lean_ctor_get(v_t_70_, 4);
v_isSharedCheck_356_ = !lean_is_exclusive(v_t_70_);
if (v_isSharedCheck_356_ == 0)
{
v___x_77_ = v_t_70_;
v_isShared_78_ = v_isSharedCheck_356_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_r_75_);
lean_inc(v_l_74_);
lean_inc(v_v_73_);
lean_inc(v_k_72_);
lean_inc(v_size_71_);
lean_dec(v_t_70_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_356_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
lean_inc_ref(v_cmp_67_);
lean_inc(v_k_72_);
lean_inc(v_k_68_);
v___x_79_ = lean_apply_2(v_cmp_67_, v_k_68_, v_k_72_);
v___x_80_ = lean_unbox(v___x_79_);
switch(v___x_80_)
{
case 0:
{
lean_object* v_impl_81_; lean_object* v___x_82_; 
lean_dec(v_size_71_);
v_impl_81_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_67_, v_k_68_, v_v_69_, v_l_74_);
v___x_82_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_75_) == 0)
{
lean_object* v_size_83_; lean_object* v_size_84_; lean_object* v_k_85_; lean_object* v_v_86_; lean_object* v_l_87_; lean_object* v_r_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_size_83_ = lean_ctor_get(v_r_75_, 0);
v_size_84_ = lean_ctor_get(v_impl_81_, 0);
lean_inc(v_size_84_);
v_k_85_ = lean_ctor_get(v_impl_81_, 1);
lean_inc(v_k_85_);
v_v_86_ = lean_ctor_get(v_impl_81_, 2);
lean_inc(v_v_86_);
v_l_87_ = lean_ctor_get(v_impl_81_, 3);
lean_inc(v_l_87_);
v_r_88_ = lean_ctor_get(v_impl_81_, 4);
lean_inc(v_r_88_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_mul(v___x_89_, v_size_83_);
v___x_91_ = lean_nat_dec_lt(v___x_90_, v_size_84_);
lean_dec(v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
lean_dec(v_r_88_);
lean_dec(v_l_87_);
lean_dec(v_v_86_);
lean_dec(v_k_85_);
v___x_92_ = lean_nat_add(v___x_82_, v_size_84_);
lean_dec(v_size_84_);
v___x_93_ = lean_nat_add(v___x_92_, v_size_83_);
lean_dec(v___x_92_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 3, v_impl_81_);
lean_ctor_set(v___x_77_, 0, v___x_93_);
v___x_95_ = v___x_77_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_96_, 3, v_impl_81_);
lean_ctor_set(v_reuseFailAlloc_96_, 4, v_r_75_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_162_; 
v_isSharedCheck_162_ = !lean_is_exclusive(v_impl_81_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; lean_object* v_unused_164_; lean_object* v_unused_165_; lean_object* v_unused_166_; lean_object* v_unused_167_; 
v_unused_163_ = lean_ctor_get(v_impl_81_, 4);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_impl_81_, 3);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_impl_81_, 2);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_impl_81_, 1);
lean_dec(v_unused_166_);
v_unused_167_ = lean_ctor_get(v_impl_81_, 0);
lean_dec(v_unused_167_);
v___x_98_ = v_impl_81_;
v_isShared_99_ = v_isSharedCheck_162_;
goto v_resetjp_97_;
}
else
{
lean_dec(v_impl_81_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_162_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_size_100_; lean_object* v_size_101_; lean_object* v_k_102_; lean_object* v_v_103_; lean_object* v_l_104_; lean_object* v_r_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_size_100_ = lean_ctor_get(v_l_87_, 0);
v_size_101_ = lean_ctor_get(v_r_88_, 0);
v_k_102_ = lean_ctor_get(v_r_88_, 1);
v_v_103_ = lean_ctor_get(v_r_88_, 2);
v_l_104_ = lean_ctor_get(v_r_88_, 3);
v_r_105_ = lean_ctor_get(v_r_88_, 4);
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = lean_nat_mul(v___x_106_, v_size_100_);
v___x_108_ = lean_nat_dec_lt(v_size_101_, v___x_107_);
lean_dec(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_137_; 
lean_inc(v_r_105_);
lean_inc(v_l_104_);
lean_inc(v_v_103_);
lean_inc(v_k_102_);
v_isSharedCheck_137_ = !lean_is_exclusive(v_r_88_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; lean_object* v_unused_139_; lean_object* v_unused_140_; lean_object* v_unused_141_; lean_object* v_unused_142_; 
v_unused_138_ = lean_ctor_get(v_r_88_, 4);
lean_dec(v_unused_138_);
v_unused_139_ = lean_ctor_get(v_r_88_, 3);
lean_dec(v_unused_139_);
v_unused_140_ = lean_ctor_get(v_r_88_, 2);
lean_dec(v_unused_140_);
v_unused_141_ = lean_ctor_get(v_r_88_, 1);
lean_dec(v_unused_141_);
v_unused_142_ = lean_ctor_get(v_r_88_, 0);
lean_dec(v_unused_142_);
v___x_110_ = v_r_88_;
v_isShared_111_ = v_isSharedCheck_137_;
goto v_resetjp_109_;
}
else
{
lean_dec(v_r_88_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_137_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___y_115_; lean_object* v___y_116_; lean_object* v___y_117_; lean_object* v___x_125_; lean_object* v___y_127_; 
v___x_112_ = lean_nat_add(v___x_82_, v_size_84_);
lean_dec(v_size_84_);
v___x_113_ = lean_nat_add(v___x_112_, v_size_83_);
lean_dec(v___x_112_);
v___x_125_ = lean_nat_add(v___x_82_, v_size_100_);
if (lean_obj_tag(v_l_104_) == 0)
{
lean_object* v_size_135_; 
v_size_135_ = lean_ctor_get(v_l_104_, 0);
lean_inc(v_size_135_);
v___y_127_ = v_size_135_;
goto v___jp_126_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___y_127_ = v___x_136_;
goto v___jp_126_;
}
v___jp_114_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_nat_add(v___y_115_, v___y_117_);
lean_dec(v___y_117_);
lean_dec(v___y_115_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 4, v_r_75_);
lean_ctor_set(v___x_110_, 3, v_r_105_);
lean_ctor_set(v___x_110_, 2, v_v_73_);
lean_ctor_set(v___x_110_, 1, v_k_72_);
lean_ctor_set(v___x_110_, 0, v___x_118_);
v___x_120_ = v___x_110_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_124_, 3, v_r_105_);
lean_ctor_set(v_reuseFailAlloc_124_, 4, v_r_75_);
v___x_120_ = v_reuseFailAlloc_124_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_122_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v___x_120_);
lean_ctor_set(v___x_98_, 3, v___y_116_);
lean_ctor_set(v___x_98_, 2, v_v_103_);
lean_ctor_set(v___x_98_, 1, v_k_102_);
lean_ctor_set(v___x_98_, 0, v___x_113_);
v___x_122_ = v___x_98_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_113_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_k_102_);
lean_ctor_set(v_reuseFailAlloc_123_, 2, v_v_103_);
lean_ctor_set(v_reuseFailAlloc_123_, 3, v___y_116_);
lean_ctor_set(v_reuseFailAlloc_123_, 4, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_nat_add(v___x_125_, v___y_127_);
lean_dec(v___y_127_);
lean_dec(v___x_125_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_l_104_);
lean_ctor_set(v___x_77_, 3, v_l_87_);
lean_ctor_set(v___x_77_, 2, v_v_86_);
lean_ctor_set(v___x_77_, 1, v_k_85_);
lean_ctor_set(v___x_77_, 0, v___x_128_);
v___x_130_ = v___x_77_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_k_85_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_v_86_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_l_87_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_l_104_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; 
v___x_131_ = lean_nat_add(v___x_82_, v_size_83_);
if (lean_obj_tag(v_r_105_) == 0)
{
lean_object* v_size_132_; 
v_size_132_ = lean_ctor_get(v_r_105_, 0);
lean_inc(v_size_132_);
v___y_115_ = v___x_131_;
v___y_116_ = v___x_130_;
v___y_117_ = v_size_132_;
goto v___jp_114_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___y_115_ = v___x_131_;
v___y_116_ = v___x_130_;
v___y_117_ = v___x_133_;
goto v___jp_114_;
}
}
}
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
lean_del_object(v___x_77_);
v___x_143_ = lean_nat_add(v___x_82_, v_size_84_);
lean_dec(v_size_84_);
v___x_144_ = lean_nat_add(v___x_143_, v_size_83_);
lean_dec(v___x_143_);
v___x_145_ = lean_nat_add(v___x_82_, v_size_83_);
v___x_146_ = lean_nat_add(v___x_145_, v_size_101_);
lean_dec(v___x_145_);
lean_inc_ref(v_r_75_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 4, v_r_75_);
lean_ctor_set(v___x_98_, 3, v_r_88_);
lean_ctor_set(v___x_98_, 2, v_v_73_);
lean_ctor_set(v___x_98_, 1, v_k_72_);
lean_ctor_set(v___x_98_, 0, v___x_146_);
v___x_148_ = v___x_98_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_146_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_161_, 3, v_r_88_);
lean_ctor_set(v_reuseFailAlloc_161_, 4, v_r_75_);
v___x_148_ = v_reuseFailAlloc_161_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_isSharedCheck_155_ = !lean_is_exclusive(v_r_75_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; lean_object* v_unused_157_; lean_object* v_unused_158_; lean_object* v_unused_159_; lean_object* v_unused_160_; 
v_unused_156_ = lean_ctor_get(v_r_75_, 4);
lean_dec(v_unused_156_);
v_unused_157_ = lean_ctor_get(v_r_75_, 3);
lean_dec(v_unused_157_);
v_unused_158_ = lean_ctor_get(v_r_75_, 2);
lean_dec(v_unused_158_);
v_unused_159_ = lean_ctor_get(v_r_75_, 1);
lean_dec(v_unused_159_);
v_unused_160_ = lean_ctor_get(v_r_75_, 0);
lean_dec(v_unused_160_);
v___x_150_ = v_r_75_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_dec(v_r_75_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 4, v___x_148_);
lean_ctor_set(v___x_150_, 3, v_l_87_);
lean_ctor_set(v___x_150_, 2, v_v_86_);
lean_ctor_set(v___x_150_, 1, v_k_85_);
lean_ctor_set(v___x_150_, 0, v___x_144_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_k_85_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_v_86_);
lean_ctor_set(v_reuseFailAlloc_154_, 3, v_l_87_);
lean_ctor_set(v_reuseFailAlloc_154_, 4, v___x_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_168_; 
v_l_168_ = lean_ctor_get(v_impl_81_, 3);
lean_inc(v_l_168_);
if (lean_obj_tag(v_l_168_) == 0)
{
lean_object* v_r_169_; lean_object* v_k_170_; lean_object* v_v_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_182_; 
v_r_169_ = lean_ctor_get(v_impl_81_, 4);
v_k_170_ = lean_ctor_get(v_impl_81_, 1);
v_v_171_ = lean_ctor_get(v_impl_81_, 2);
v_isSharedCheck_182_ = !lean_is_exclusive(v_impl_81_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; lean_object* v_unused_184_; 
v_unused_183_ = lean_ctor_get(v_impl_81_, 3);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_impl_81_, 0);
lean_dec(v_unused_184_);
v___x_173_ = v_impl_81_;
v_isShared_174_ = v_isSharedCheck_182_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_r_169_);
lean_inc(v_v_171_);
lean_inc(v_k_170_);
lean_dec(v_impl_81_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_182_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_169_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 3, v_r_169_);
lean_ctor_set(v___x_173_, 2, v_v_73_);
lean_ctor_set(v___x_173_, 1, v_k_72_);
lean_ctor_set(v___x_173_, 0, v___x_82_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_181_, 3, v_r_169_);
lean_ctor_set(v_reuseFailAlloc_181_, 4, v_r_169_);
v___x_177_ = v_reuseFailAlloc_181_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_179_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_177_);
lean_ctor_set(v___x_77_, 3, v_l_168_);
lean_ctor_set(v___x_77_, 2, v_v_171_);
lean_ctor_set(v___x_77_, 1, v_k_170_);
lean_ctor_set(v___x_77_, 0, v___x_175_);
v___x_179_ = v___x_77_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_k_170_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_v_171_);
lean_ctor_set(v_reuseFailAlloc_180_, 3, v_l_168_);
lean_ctor_set(v_reuseFailAlloc_180_, 4, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_r_185_; 
v_r_185_ = lean_ctor_get(v_impl_81_, 4);
lean_inc(v_r_185_);
if (lean_obj_tag(v_r_185_) == 0)
{
lean_object* v_k_186_; lean_object* v_v_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_210_; 
v_k_186_ = lean_ctor_get(v_impl_81_, 1);
v_v_187_ = lean_ctor_get(v_impl_81_, 2);
v_isSharedCheck_210_ = !lean_is_exclusive(v_impl_81_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; 
v_unused_211_ = lean_ctor_get(v_impl_81_, 4);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_impl_81_, 3);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_impl_81_, 0);
lean_dec(v_unused_213_);
v___x_189_ = v_impl_81_;
v_isShared_190_ = v_isSharedCheck_210_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_v_187_);
lean_inc(v_k_186_);
lean_dec(v_impl_81_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_210_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_k_191_; lean_object* v_v_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_206_; 
v_k_191_ = lean_ctor_get(v_r_185_, 1);
v_v_192_ = lean_ctor_get(v_r_185_, 2);
v_isSharedCheck_206_ = !lean_is_exclusive(v_r_185_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; lean_object* v_unused_208_; lean_object* v_unused_209_; 
v_unused_207_ = lean_ctor_get(v_r_185_, 4);
lean_dec(v_unused_207_);
v_unused_208_ = lean_ctor_get(v_r_185_, 3);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_r_185_, 0);
lean_dec(v_unused_209_);
v___x_194_ = v_r_185_;
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_v_192_);
lean_inc(v_k_191_);
lean_dec(v_r_185_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = lean_unsigned_to_nat(3u);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 4, v_l_168_);
lean_ctor_set(v___x_194_, 3, v_l_168_);
lean_ctor_set(v___x_194_, 2, v_v_187_);
lean_ctor_set(v___x_194_, 1, v_k_186_);
lean_ctor_set(v___x_194_, 0, v___x_82_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_k_186_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_v_187_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_l_168_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_l_168_);
v___x_198_ = v_reuseFailAlloc_205_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v_l_168_);
lean_ctor_set(v___x_189_, 2, v_v_73_);
lean_ctor_set(v___x_189_, 1, v_k_72_);
lean_ctor_set(v___x_189_, 0, v___x_82_);
v___x_200_ = v___x_189_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_82_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_l_168_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_l_168_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_200_);
lean_ctor_set(v___x_77_, 3, v___x_198_);
lean_ctor_set(v___x_77_, 2, v_v_192_);
lean_ctor_set(v___x_77_, 1, v_k_191_);
lean_ctor_set(v___x_77_, 0, v___x_196_);
v___x_202_ = v___x_77_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_k_191_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_v_192_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_unsigned_to_nat(2u);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_185_);
lean_ctor_set(v___x_77_, 3, v_impl_81_);
lean_ctor_set(v___x_77_, 0, v___x_214_);
v___x_216_ = v___x_77_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v_impl_81_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v_r_185_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
case 1:
{
lean_object* v___x_219_; 
lean_dec(v_v_73_);
lean_dec(v_k_72_);
lean_dec_ref(v_cmp_67_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 2, v_v_69_);
lean_ctor_set(v___x_77_, 1, v_k_68_);
v___x_219_ = v___x_77_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_size_71_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_k_68_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_v_69_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_r_75_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
default: 
{
lean_object* v_impl_221_; lean_object* v___x_222_; 
lean_dec(v_size_71_);
v_impl_221_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_67_, v_k_68_, v_v_69_, v_r_75_);
v___x_222_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_74_) == 0)
{
lean_object* v_size_223_; lean_object* v_size_224_; lean_object* v_k_225_; lean_object* v_v_226_; lean_object* v_l_227_; lean_object* v_r_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_size_223_ = lean_ctor_get(v_l_74_, 0);
v_size_224_ = lean_ctor_get(v_impl_221_, 0);
lean_inc(v_size_224_);
v_k_225_ = lean_ctor_get(v_impl_221_, 1);
lean_inc(v_k_225_);
v_v_226_ = lean_ctor_get(v_impl_221_, 2);
lean_inc(v_v_226_);
v_l_227_ = lean_ctor_get(v_impl_221_, 3);
lean_inc(v_l_227_);
v_r_228_ = lean_ctor_get(v_impl_221_, 4);
lean_inc(v_r_228_);
v___x_229_ = lean_unsigned_to_nat(3u);
v___x_230_ = lean_nat_mul(v___x_229_, v_size_223_);
v___x_231_ = lean_nat_dec_lt(v___x_230_, v_size_224_);
lean_dec(v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_r_228_);
lean_dec(v_l_227_);
lean_dec(v_v_226_);
lean_dec(v_k_225_);
v___x_232_ = lean_nat_add(v___x_222_, v_size_223_);
v___x_233_ = lean_nat_add(v___x_232_, v_size_224_);
lean_dec(v_size_224_);
lean_dec(v___x_232_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_impl_221_);
lean_ctor_set(v___x_77_, 0, v___x_233_);
v___x_235_ = v___x_77_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_impl_221_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
else
{
lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_300_; 
v_isSharedCheck_300_ = !lean_is_exclusive(v_impl_221_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_301_ = lean_ctor_get(v_impl_221_, 4);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_impl_221_, 3);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_impl_221_, 2);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_impl_221_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_impl_221_, 0);
lean_dec(v_unused_305_);
v___x_238_ = v_impl_221_;
v_isShared_239_ = v_isSharedCheck_300_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_impl_221_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_300_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_size_240_; lean_object* v_k_241_; lean_object* v_v_242_; lean_object* v_l_243_; lean_object* v_r_244_; lean_object* v_size_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_size_240_ = lean_ctor_get(v_l_227_, 0);
v_k_241_ = lean_ctor_get(v_l_227_, 1);
v_v_242_ = lean_ctor_get(v_l_227_, 2);
v_l_243_ = lean_ctor_get(v_l_227_, 3);
v_r_244_ = lean_ctor_get(v_l_227_, 4);
v_size_245_ = lean_ctor_get(v_r_228_, 0);
v___x_246_ = lean_unsigned_to_nat(2u);
v___x_247_ = lean_nat_mul(v___x_246_, v_size_245_);
v___x_248_ = lean_nat_dec_lt(v_size_240_, v___x_247_);
lean_dec(v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_276_; 
lean_inc(v_r_244_);
lean_inc(v_l_243_);
lean_inc(v_v_242_);
lean_inc(v_k_241_);
v_isSharedCheck_276_ = !lean_is_exclusive(v_l_227_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; lean_object* v_unused_281_; 
v_unused_277_ = lean_ctor_get(v_l_227_, 4);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_l_227_, 3);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_l_227_, 2);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_l_227_, 1);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_l_227_, 0);
lean_dec(v_unused_281_);
v___x_250_ = v_l_227_;
v_isShared_251_ = v_isSharedCheck_276_;
goto v_resetjp_249_;
}
else
{
lean_dec(v_l_227_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_276_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_266_; 
v___x_252_ = lean_nat_add(v___x_222_, v_size_223_);
v___x_253_ = lean_nat_add(v___x_252_, v_size_224_);
lean_dec(v_size_224_);
if (lean_obj_tag(v_l_243_) == 0)
{
lean_object* v_size_274_; 
v_size_274_ = lean_ctor_get(v_l_243_, 0);
lean_inc(v_size_274_);
v___y_266_ = v_size_274_;
goto v___jp_265_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___y_266_ = v___x_275_;
goto v___jp_265_;
}
v___jp_254_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_nat_add(v___y_255_, v___y_257_);
lean_dec(v___y_257_);
lean_dec(v___y_255_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 4, v_r_228_);
lean_ctor_set(v___x_250_, 3, v_r_244_);
lean_ctor_set(v___x_250_, 2, v_v_226_);
lean_ctor_set(v___x_250_, 1, v_k_225_);
lean_ctor_set(v___x_250_, 0, v___x_258_);
v___x_260_ = v___x_250_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_k_225_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_v_226_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v_r_244_);
lean_ctor_set(v_reuseFailAlloc_264_, 4, v_r_228_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 4, v___x_260_);
lean_ctor_set(v___x_238_, 3, v___y_256_);
lean_ctor_set(v___x_238_, 2, v_v_242_);
lean_ctor_set(v___x_238_, 1, v_k_241_);
lean_ctor_set(v___x_238_, 0, v___x_253_);
v___x_262_ = v___x_238_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_k_241_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_v_242_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v___y_256_);
lean_ctor_set(v_reuseFailAlloc_263_, 4, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_nat_add(v___x_252_, v___y_266_);
lean_dec(v___y_266_);
lean_dec(v___x_252_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_l_243_);
lean_ctor_set(v___x_77_, 0, v___x_267_);
v___x_269_ = v___x_77_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v_l_243_);
v___x_269_ = v_reuseFailAlloc_273_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; 
v___x_270_ = lean_nat_add(v___x_222_, v_size_245_);
if (lean_obj_tag(v_r_244_) == 0)
{
lean_object* v_size_271_; 
v_size_271_ = lean_ctor_get(v_r_244_, 0);
lean_inc(v_size_271_);
v___y_255_ = v___x_270_;
v___y_256_ = v___x_269_;
v___y_257_ = v_size_271_;
goto v___jp_254_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___y_255_ = v___x_270_;
v___y_256_ = v___x_269_;
v___y_257_ = v___x_272_;
goto v___jp_254_;
}
}
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
lean_del_object(v___x_77_);
v___x_282_ = lean_nat_add(v___x_222_, v_size_223_);
v___x_283_ = lean_nat_add(v___x_282_, v_size_224_);
lean_dec(v_size_224_);
v___x_284_ = lean_nat_add(v___x_282_, v_size_240_);
lean_dec(v___x_282_);
lean_inc_ref(v_l_74_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 4, v_l_227_);
lean_ctor_set(v___x_238_, 3, v_l_74_);
lean_ctor_set(v___x_238_, 2, v_v_73_);
lean_ctor_set(v___x_238_, 1, v_k_72_);
lean_ctor_set(v___x_238_, 0, v___x_284_);
v___x_286_ = v___x_238_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_299_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_299_, 3, v_l_74_);
lean_ctor_set(v_reuseFailAlloc_299_, 4, v_l_227_);
v___x_286_ = v_reuseFailAlloc_299_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_isSharedCheck_293_ = !lean_is_exclusive(v_l_74_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; lean_object* v_unused_297_; lean_object* v_unused_298_; 
v_unused_294_ = lean_ctor_get(v_l_74_, 4);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_l_74_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_74_, 2);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_l_74_, 1);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_l_74_, 0);
lean_dec(v_unused_298_);
v___x_288_ = v_l_74_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_l_74_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 4, v_r_228_);
lean_ctor_set(v___x_288_, 3, v___x_286_);
lean_ctor_set(v___x_288_, 2, v_v_226_);
lean_ctor_set(v___x_288_, 1, v_k_225_);
lean_ctor_set(v___x_288_, 0, v___x_283_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_k_225_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_v_226_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_r_228_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_306_; 
v_l_306_ = lean_ctor_get(v_impl_221_, 3);
lean_inc(v_l_306_);
if (lean_obj_tag(v_l_306_) == 0)
{
lean_object* v_r_307_; lean_object* v_k_308_; lean_object* v_v_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_332_; 
v_r_307_ = lean_ctor_get(v_impl_221_, 4);
v_k_308_ = lean_ctor_get(v_impl_221_, 1);
v_v_309_ = lean_ctor_get(v_impl_221_, 2);
v_isSharedCheck_332_ = !lean_is_exclusive(v_impl_221_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_333_ = lean_ctor_get(v_impl_221_, 3);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_impl_221_, 0);
lean_dec(v_unused_334_);
v___x_311_ = v_impl_221_;
v_isShared_312_ = v_isSharedCheck_332_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_r_307_);
lean_inc(v_v_309_);
lean_inc(v_k_308_);
lean_dec(v_impl_221_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_332_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v_k_313_; lean_object* v_v_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_328_; 
v_k_313_ = lean_ctor_get(v_l_306_, 1);
v_v_314_ = lean_ctor_get(v_l_306_, 2);
v_isSharedCheck_328_ = !lean_is_exclusive(v_l_306_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_329_ = lean_ctor_get(v_l_306_, 4);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_l_306_, 3);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_l_306_, 0);
lean_dec(v_unused_331_);
v___x_316_ = v_l_306_;
v_isShared_317_ = v_isSharedCheck_328_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_v_314_);
lean_inc(v_k_313_);
lean_dec(v_l_306_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_328_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_307_, 2);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 4, v_r_307_);
lean_ctor_set(v___x_316_, 3, v_r_307_);
lean_ctor_set(v___x_316_, 2, v_v_73_);
lean_ctor_set(v___x_316_, 1, v_k_72_);
lean_ctor_set(v___x_316_, 0, v___x_222_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_r_307_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_r_307_);
v___x_320_ = v_reuseFailAlloc_327_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
lean_inc(v_r_307_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 3, v_r_307_);
lean_ctor_set(v___x_311_, 0, v___x_222_);
v___x_322_ = v___x_311_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_k_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_v_309_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_r_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_r_307_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v___x_322_);
lean_ctor_set(v___x_77_, 3, v___x_320_);
lean_ctor_set(v___x_77_, 2, v_v_314_);
lean_ctor_set(v___x_77_, 1, v_k_313_);
lean_ctor_set(v___x_77_, 0, v___x_318_);
v___x_324_ = v___x_77_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_313_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
else
{
lean_object* v_r_335_; 
v_r_335_ = lean_ctor_get(v_impl_221_, 4);
lean_inc(v_r_335_);
if (lean_obj_tag(v_r_335_) == 0)
{
lean_object* v_k_336_; lean_object* v_v_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_348_; 
v_k_336_ = lean_ctor_get(v_impl_221_, 1);
v_v_337_ = lean_ctor_get(v_impl_221_, 2);
v_isSharedCheck_348_ = !lean_is_exclusive(v_impl_221_);
if (v_isSharedCheck_348_ == 0)
{
lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; 
v_unused_349_ = lean_ctor_get(v_impl_221_, 4);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_impl_221_, 3);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_impl_221_, 0);
lean_dec(v_unused_351_);
v___x_339_ = v_impl_221_;
v_isShared_340_ = v_isSharedCheck_348_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_v_337_);
lean_inc(v_k_336_);
lean_dec(v_impl_221_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_348_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_unsigned_to_nat(3u);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 4, v_l_306_);
lean_ctor_set(v___x_339_, 2, v_v_73_);
lean_ctor_set(v___x_339_, 1, v_k_72_);
lean_ctor_set(v___x_339_, 0, v___x_222_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_l_306_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_l_306_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_r_335_);
lean_ctor_set(v___x_77_, 3, v___x_343_);
lean_ctor_set(v___x_77_, 2, v_v_337_);
lean_ctor_set(v___x_77_, 1, v_k_336_);
lean_ctor_set(v___x_77_, 0, v___x_341_);
v___x_345_ = v___x_77_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_336_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_337_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v_r_335_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_unsigned_to_nat(2u);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 4, v_impl_221_);
lean_ctor_set(v___x_77_, 3, v_r_335_);
lean_ctor_set(v___x_77_, 0, v___x_352_);
v___x_354_ = v___x_77_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_k_72_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_v_73_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_r_335_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_impl_221_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec_ref(v_cmp_67_);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_k_68_);
lean_ctor_set(v___x_358_, 2, v_v_69_);
lean_ctor_set(v___x_358_, 3, v_t_70_);
lean_ctor_set(v___x_358_, 4, v_t_70_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(lean_object* v_items_359_, lean_object* v_cmp_360_, lean_object* v_n_361_, lean_object* v_j_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_zero_364_; uint8_t v_isZero_365_; 
v_zero_364_ = lean_unsigned_to_nat(0u);
v_isZero_365_ = lean_nat_dec_eq(v_j_362_, v_zero_364_);
if (v_isZero_365_ == 1)
{
lean_dec(v_j_362_);
lean_dec_ref(v_cmp_360_);
return v_a_363_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_fst_368_; lean_object* v_one_369_; lean_object* v_n_370_; lean_object* v___x_371_; 
v___x_366_ = lean_nat_sub(v_n_361_, v_j_362_);
v___x_367_ = lean_array_fget_borrowed(v_items_359_, v___x_366_);
v_fst_368_ = lean_ctor_get(v___x_367_, 0);
v_one_369_ = lean_unsigned_to_nat(1u);
v_n_370_ = lean_nat_sub(v_j_362_, v_one_369_);
lean_dec(v_j_362_);
lean_inc(v_fst_368_);
lean_inc_ref(v_cmp_360_);
v___x_371_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_360_, v_fst_368_, v___x_366_, v_a_363_);
v_j_362_ = v_n_370_;
v_a_363_ = v___x_371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg___boxed(lean_object* v_items_373_, lean_object* v_cmp_374_, lean_object* v_n_375_, lean_object* v_j_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_373_, v_cmp_374_, v_n_375_, v_j_376_, v_a_377_);
lean_dec(v_n_375_);
lean_dec_ref(v_items_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray___redArg(lean_object* v_cmp_379_, lean_object* v_items_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_indices_383_; lean_object* v___x_384_; 
v___x_381_ = lean_array_get_size(v_items_380_);
v___x_382_ = lean_box(1);
v_indices_383_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_380_, v_cmp_379_, v___x_381_, v___x_381_, v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_items_380_);
lean_ctor_set(v___x_384_, 1, v_indices_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray(lean_object* v_00_u03b1_385_, lean_object* v_00_u03b2_386_, lean_object* v_cmp_387_, lean_object* v_items_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lake_Toml_RBDict_ofArray___redArg(v_cmp_387_, v_items_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0(lean_object* v_00_u03b1_390_, lean_object* v_cmp_391_, lean_object* v_00_u03b2_392_, lean_object* v_k_393_, lean_object* v_v_394_, lean_object* v_t_395_, lean_object* v_hl_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_391_, v_k_393_, v_v_394_, v_t_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b2_399_, lean_object* v_items_400_, lean_object* v_cmp_401_, lean_object* v_n_402_, lean_object* v_j_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_400_, v_cmp_401_, v_n_402_, v_j_403_, v_a_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___boxed(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_items_409_, lean_object* v_cmp_410_, lean_object* v_n_411_, lean_object* v_j_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(v_00_u03b1_407_, v_00_u03b2_408_, v_items_409_, v_cmp_410_, v_n_411_, v_j_412_, v_a_413_, v_a_414_);
lean_dec(v_n_411_);
lean_dec_ref(v_items_409_);
return v_res_415_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___redArg(lean_object* v_inst_416_, lean_object* v_self_417_, lean_object* v_other_418_){
_start:
{
lean_object* v_items_419_; lean_object* v_items_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_items_419_ = lean_ctor_get(v_self_417_, 0);
v_items_420_ = lean_ctor_get(v_other_418_, 0);
v___x_421_ = lean_array_get_size(v_items_419_);
v___x_422_ = lean_array_get_size(v_items_420_);
v___x_423_ = lean_nat_dec_eq(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
lean_dec_ref(v_inst_416_);
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = l_Array_isEqvAux___redArg(v_items_419_, v_items_420_, v_inst_416_, v___x_421_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___redArg___boxed(lean_object* v_inst_425_, lean_object* v_self_426_, lean_object* v_other_427_){
_start:
{
uint8_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_425_, v_self_426_, v_other_427_);
lean_dec_ref(v_other_427_);
lean_dec_ref(v_self_426_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq(lean_object* v_00_u03b1_430_, lean_object* v_00_u03b2_431_, lean_object* v_cmp_432_, lean_object* v_inst_433_, lean_object* v_self_434_, lean_object* v_other_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_433_, v_self_434_, v_other_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___boxed(lean_object* v_00_u03b1_437_, lean_object* v_00_u03b2_438_, lean_object* v_cmp_439_, lean_object* v_inst_440_, lean_object* v_self_441_, lean_object* v_other_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lake_Toml_RBDict_beq(v_00_u03b1_437_, v_00_u03b2_438_, v_cmp_439_, v_inst_440_, v_self_441_, v_other_442_);
lean_dec_ref(v_other_442_);
lean_dec_ref(v_self_441_);
lean_dec_ref(v_cmp_439_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd___redArg(lean_object* v_cmp_445_, lean_object* v_inst_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_beq___boxed), 6, 4);
lean_closure_set(v___x_447_, 0, lean_box(0));
lean_closure_set(v___x_447_, 1, lean_box(0));
lean_closure_set(v___x_447_, 2, v_cmp_445_);
lean_closure_set(v___x_447_, 3, v_inst_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_cmp_450_, lean_object* v_inst_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_beq___boxed), 6, 4);
lean_closure_set(v___x_452_, 0, lean_box(0));
lean_closure_set(v___x_452_, 1, lean_box(0));
lean_closure_set(v___x_452_, 2, v_cmp_450_);
lean_closure_set(v___x_452_, 3, v_inst_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg(lean_object* v_t_453_){
_start:
{
lean_object* v_items_454_; lean_object* v___x_455_; 
v_items_454_ = lean_ctor_get(v_t_453_, 0);
v___x_455_ = lean_array_get_size(v_items_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg___boxed(lean_object* v_t_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lake_Toml_RBDict_size___redArg(v_t_456_);
lean_dec_ref(v_t_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_cmp_460_, lean_object* v_t_461_){
_start:
{
lean_object* v_items_462_; lean_object* v___x_463_; 
v_items_462_ = lean_ctor_get(v_t_461_, 0);
v___x_463_ = lean_array_get_size(v_items_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___boxed(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_cmp_466_, lean_object* v_t_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lake_Toml_RBDict_size(v_00_u03b1_464_, v_00_u03b2_465_, v_cmp_466_, v_t_467_);
lean_dec_ref(v_t_467_);
lean_dec_ref(v_cmp_466_);
return v_res_468_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_isEmpty___redArg(lean_object* v_t_469_){
_start:
{
lean_object* v_items_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_items_470_ = lean_ctor_get(v_t_469_, 0);
v___x_471_ = lean_array_get_size(v_items_470_);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___redArg___boxed(lean_object* v_t_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Lake_Toml_RBDict_isEmpty___redArg(v_t_474_);
lean_dec_ref(v_t_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_isEmpty(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_cmp_479_, lean_object* v_t_480_){
_start:
{
lean_object* v_items_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_items_481_ = lean_ctor_get(v_t_480_, 0);
v___x_482_ = lean_array_get_size(v_items_481_);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___boxed(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_cmp_487_, lean_object* v_t_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Lake_Toml_RBDict_isEmpty(v_00_u03b1_485_, v_00_u03b2_486_, v_cmp_487_, v_t_488_);
lean_dec_ref(v_t_488_);
lean_dec_ref(v_cmp_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(size_t v_sz_491_, size_t v_i_492_, lean_object* v_bs_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_494_ == 0)
{
return v_bs_493_;
}
else
{
lean_object* v_v_495_; lean_object* v_fst_496_; lean_object* v___x_497_; lean_object* v_bs_x27_498_; size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; 
v_v_495_ = lean_array_uget_borrowed(v_bs_493_, v_i_492_);
v_fst_496_ = lean_ctor_get(v_v_495_, 0);
lean_inc(v_fst_496_);
v___x_497_ = lean_unsigned_to_nat(0u);
v_bs_x27_498_ = lean_array_uset(v_bs_493_, v_i_492_, v___x_497_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_492_, v___x_499_);
v___x_501_ = lean_array_uset(v_bs_x27_498_, v_i_492_, v_fst_496_);
v_i_492_ = v___x_500_;
v_bs_493_ = v___x_501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg___boxed(lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_bs_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_507_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_boxed_506_, v_i_boxed_507_, v_bs_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___redArg(lean_object* v_t_509_){
_start:
{
lean_object* v_items_510_; size_t v_sz_511_; size_t v___x_512_; lean_object* v___x_513_; 
v_items_510_ = lean_ctor_get(v_t_509_, 0);
lean_inc_ref(v_items_510_);
lean_dec_ref(v_t_509_);
v_sz_511_ = lean_array_size(v_items_510_);
v___x_512_ = ((size_t)0ULL);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_511_, v___x_512_, v_items_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_cmp_516_, lean_object* v_t_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lake_Toml_RBDict_keys___redArg(v_t_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___boxed(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_cmp_521_, lean_object* v_t_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lake_Toml_RBDict_keys(v_00_u03b1_519_, v_00_u03b2_520_, v_cmp_521_, v_t_522_);
lean_dec_ref(v_cmp_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, size_t v_sz_526_, size_t v_i_527_, lean_object* v_bs_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_526_, v_i_527_, v_bs_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___boxed(lean_object* v_00_u03b1_530_, lean_object* v_00_u03b2_531_, lean_object* v_sz_532_, lean_object* v_i_533_, lean_object* v_bs_534_){
_start:
{
size_t v_sz_boxed_535_; size_t v_i_boxed_536_; lean_object* v_res_537_; 
v_sz_boxed_535_ = lean_unbox_usize(v_sz_532_);
lean_dec(v_sz_532_);
v_i_boxed_536_ = lean_unbox_usize(v_i_533_);
lean_dec(v_i_533_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(v_00_u03b1_530_, v_00_u03b2_531_, v_sz_boxed_535_, v_i_boxed_536_, v_bs_534_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(size_t v_sz_538_, size_t v_i_539_, lean_object* v_bs_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_541_ == 0)
{
return v_bs_540_;
}
else
{
lean_object* v_v_542_; lean_object* v_snd_543_; lean_object* v___x_544_; lean_object* v_bs_x27_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_v_542_ = lean_array_uget_borrowed(v_bs_540_, v_i_539_);
v_snd_543_ = lean_ctor_get(v_v_542_, 1);
lean_inc(v_snd_543_);
v___x_544_ = lean_unsigned_to_nat(0u);
v_bs_x27_545_ = lean_array_uset(v_bs_540_, v_i_539_, v___x_544_);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_539_, v___x_546_);
v___x_548_ = lean_array_uset(v_bs_x27_545_, v_i_539_, v_snd_543_);
v_i_539_ = v___x_547_;
v_bs_540_ = v___x_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg___boxed(lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_bs_552_){
_start:
{
size_t v_sz_boxed_553_; size_t v_i_boxed_554_; lean_object* v_res_555_; 
v_sz_boxed_553_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_boxed_553_, v_i_boxed_554_, v_bs_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___redArg(lean_object* v_t_556_){
_start:
{
lean_object* v_items_557_; size_t v_sz_558_; size_t v___x_559_; lean_object* v___x_560_; 
v_items_557_ = lean_ctor_get(v_t_556_, 0);
lean_inc_ref(v_items_557_);
lean_dec_ref(v_t_556_);
v_sz_558_ = lean_array_size(v_items_557_);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_558_, v___x_559_, v_items_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_cmp_563_, lean_object* v_t_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lake_Toml_RBDict_values___redArg(v_t_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___boxed(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_cmp_568_, lean_object* v_t_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lake_Toml_RBDict_values(v_00_u03b1_566_, v_00_u03b2_567_, v_cmp_568_, v_t_569_);
lean_dec_ref(v_cmp_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, size_t v_sz_573_, size_t v_i_574_, lean_object* v_bs_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_573_, v_i_574_, v_bs_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___boxed(lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_sz_579_, lean_object* v_i_580_, lean_object* v_bs_581_){
_start:
{
size_t v_sz_boxed_582_; size_t v_i_boxed_583_; lean_object* v_res_584_; 
v_sz_boxed_582_ = lean_unbox_usize(v_sz_579_);
lean_dec(v_sz_579_);
v_i_boxed_583_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(v_00_u03b1_577_, v_00_u03b2_578_, v_sz_boxed_582_, v_i_boxed_583_, v_bs_581_);
return v_res_584_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(lean_object* v_cmp_585_, lean_object* v_k_586_, lean_object* v_t_587_){
_start:
{
if (lean_obj_tag(v_t_587_) == 0)
{
lean_object* v_k_588_; lean_object* v_l_589_; lean_object* v_r_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_k_588_ = lean_ctor_get(v_t_587_, 1);
lean_inc(v_k_588_);
v_l_589_ = lean_ctor_get(v_t_587_, 3);
lean_inc(v_l_589_);
v_r_590_ = lean_ctor_get(v_t_587_, 4);
lean_inc(v_r_590_);
lean_dec_ref(v_t_587_);
lean_inc_ref(v_cmp_585_);
lean_inc(v_k_586_);
v___x_591_ = lean_apply_2(v_cmp_585_, v_k_586_, v_k_588_);
v___x_592_ = lean_unbox(v___x_591_);
switch(v___x_592_)
{
case 0:
{
lean_dec(v_r_590_);
v_t_587_ = v_l_589_;
goto _start;
}
case 1:
{
uint8_t v___x_594_; 
lean_dec(v_r_590_);
lean_dec(v_l_589_);
lean_dec(v_k_586_);
lean_dec_ref(v_cmp_585_);
v___x_594_ = 1;
return v___x_594_;
}
default: 
{
lean_dec(v_l_589_);
v_t_587_ = v_r_590_;
goto _start;
}
}
}
else
{
uint8_t v___x_596_; 
lean_dec(v_k_586_);
lean_dec_ref(v_cmp_585_);
v___x_596_ = 0;
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg___boxed(lean_object* v_cmp_597_, lean_object* v_k_598_, lean_object* v_t_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_597_, v_k_598_, v_t_599_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object* v_cmp_602_, lean_object* v_k_603_, lean_object* v_t_604_){
_start:
{
lean_object* v_indices_605_; uint8_t v___x_606_; 
v_indices_605_ = lean_ctor_get(v_t_604_, 1);
lean_inc(v_indices_605_);
lean_dec_ref(v_t_604_);
v___x_606_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_602_, v_k_603_, v_indices_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___redArg___boxed(lean_object* v_cmp_607_, lean_object* v_k_608_, lean_object* v_t_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_607_, v_k_608_, v_t_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_contains(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_cmp_614_, lean_object* v_k_615_, lean_object* v_t_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_614_, v_k_615_, v_t_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___boxed(lean_object* v_00_u03b1_618_, lean_object* v_00_u03b2_619_, lean_object* v_cmp_620_, lean_object* v_k_621_, lean_object* v_t_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Lake_Toml_RBDict_contains(v_00_u03b1_618_, v_00_u03b2_619_, v_cmp_620_, v_k_621_, v_t_622_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(lean_object* v_00_u03b1_625_, lean_object* v_cmp_626_, lean_object* v_00_u03b2_627_, lean_object* v_k_628_, lean_object* v_t_629_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_626_, v_k_628_, v_t_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___boxed(lean_object* v_00_u03b1_631_, lean_object* v_cmp_632_, lean_object* v_00_u03b2_633_, lean_object* v_k_634_, lean_object* v_t_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(v_00_u03b1_631_, v_cmp_632_, v_00_u03b2_633_, v_k_634_, v_t_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(lean_object* v_cmp_638_, lean_object* v_t_639_, lean_object* v_k_640_){
_start:
{
if (lean_obj_tag(v_t_639_) == 0)
{
lean_object* v_k_641_; lean_object* v_v_642_; lean_object* v_l_643_; lean_object* v_r_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_k_641_ = lean_ctor_get(v_t_639_, 1);
lean_inc(v_k_641_);
v_v_642_ = lean_ctor_get(v_t_639_, 2);
lean_inc(v_v_642_);
v_l_643_ = lean_ctor_get(v_t_639_, 3);
lean_inc(v_l_643_);
v_r_644_ = lean_ctor_get(v_t_639_, 4);
lean_inc(v_r_644_);
lean_dec_ref(v_t_639_);
lean_inc_ref(v_cmp_638_);
lean_inc(v_k_640_);
v___x_645_ = lean_apply_2(v_cmp_638_, v_k_640_, v_k_641_);
v___x_646_ = lean_unbox(v___x_645_);
switch(v___x_646_)
{
case 0:
{
lean_dec(v_r_644_);
lean_dec(v_v_642_);
v_t_639_ = v_l_643_;
goto _start;
}
case 1:
{
lean_object* v___x_648_; 
lean_dec(v_r_644_);
lean_dec(v_l_643_);
lean_dec(v_k_640_);
lean_dec_ref(v_cmp_638_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v_v_642_);
return v___x_648_;
}
default: 
{
lean_dec(v_l_643_);
lean_dec(v_v_642_);
v_t_639_ = v_r_644_;
goto _start;
}
}
}
else
{
lean_object* v___x_650_; 
lean_dec(v_k_640_);
lean_dec_ref(v_cmp_638_);
v___x_650_ = lean_box(0);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f___redArg(lean_object* v_cmp_651_, lean_object* v_k_652_, lean_object* v_t_653_){
_start:
{
lean_object* v_items_654_; lean_object* v_indices_655_; lean_object* v___x_656_; 
v_items_654_ = lean_ctor_get(v_t_653_, 0);
lean_inc_ref(v_items_654_);
v_indices_655_ = lean_ctor_get(v_t_653_, 1);
lean_inc(v_indices_655_);
lean_dec_ref(v_t_653_);
v___x_656_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_651_, v_indices_655_, v_k_652_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v___x_657_; 
lean_dec_ref(v_items_654_);
v___x_657_ = lean_box(0);
return v___x_657_;
}
else
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v_val_658_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_668_ == 0)
{
v___x_660_ = v___x_656_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v___x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_array_get_size(v_items_654_);
lean_dec_ref(v_items_654_);
v___x_663_ = lean_nat_dec_lt(v_val_658_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_del_object(v___x_660_);
lean_dec(v_val_658_);
v___x_664_ = lean_box(0);
return v___x_664_;
}
else
{
lean_object* v___x_666_; 
if (v_isShared_661_ == 0)
{
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_val_658_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f(lean_object* v_00_u03b1_669_, lean_object* v_00_u03b2_670_, lean_object* v_cmp_671_, lean_object* v_k_672_, lean_object* v_t_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_671_, v_k_672_, v_t_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0(lean_object* v_00_u03b1_675_, lean_object* v_cmp_676_, lean_object* v_00_u03b4_677_, lean_object* v_t_678_, lean_object* v_k_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_676_, v_t_678_, v_k_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object* v_cmp_681_, lean_object* v_k_682_, lean_object* v_t_683_){
_start:
{
lean_object* v___x_684_; 
lean_inc_ref(v_t_683_);
v___x_684_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_681_, v_k_682_, v_t_683_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v___x_685_; 
lean_dec_ref(v_t_683_);
v___x_685_ = lean_box(0);
return v___x_685_;
}
else
{
lean_object* v_val_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v_val_686_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v___x_684_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_val_686_);
lean_dec(v___x_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_items_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v_items_690_ = lean_ctor_get(v_t_683_, 0);
lean_inc_ref(v_items_690_);
lean_dec_ref(v_t_683_);
v___x_691_ = lean_array_fget(v_items_690_, v_val_686_);
lean_dec(v_val_686_);
lean_dec_ref(v_items_690_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f(lean_object* v_00_u03b1_696_, lean_object* v_00_u03b2_697_, lean_object* v_cmp_698_, lean_object* v_k_699_, lean_object* v_t_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_698_, v_k_699_, v_t_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f___redArg(lean_object* v_cmp_702_, lean_object* v_k_703_, lean_object* v_t_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_702_, v_k_703_, v_t_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_box(0);
return v___x_706_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_val_707_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v___x_705_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v___x_705_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_snd_711_; lean_object* v___x_713_; 
v_snd_711_ = lean_ctor_get(v_val_707_, 1);
lean_inc(v_snd_711_);
lean_dec(v_val_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_snd_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_snd_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f(lean_object* v_00_u03b1_716_, lean_object* v_00_u03b2_717_, lean_object* v_cmp_718_, lean_object* v_k_719_, lean_object* v_t_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_718_, v_k_719_, v_t_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_box(0);
return v___x_722_;
}
else
{
lean_object* v_val_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_731_; 
v_val_723_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_731_ == 0)
{
v___x_725_ = v___x_721_;
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_val_723_);
lean_dec(v___x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_snd_727_; lean_object* v___x_729_; 
v_snd_727_ = lean_ctor_get(v_val_723_, 1);
lean_inc(v_snd_727_);
lean_dec(v_val_723_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_snd_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_snd_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object* v_cmp_732_, lean_object* v_k_733_, lean_object* v_v_734_, lean_object* v_t_735_){
_start:
{
lean_object* v_items_736_; lean_object* v_indices_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_items_736_ = lean_ctor_get(v_t_735_, 0);
v_indices_737_ = lean_ctor_get(v_t_735_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_t_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_739_ = v_t_735_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_indices_737_);
lean_inc(v_items_736_);
lean_dec(v_t_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_inc(v_k_733_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_k_733_);
lean_ctor_set(v___x_741_, 1, v_v_734_);
lean_inc_ref(v_items_736_);
v___x_742_ = lean_array_push(v_items_736_, v___x_741_);
v___x_743_ = lean_array_get_size(v_items_736_);
lean_dec_ref(v_items_736_);
v___x_744_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_732_, v_k_733_, v___x_743_, v_indices_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_744_);
lean_ctor_set(v___x_739_, 0, v___x_742_);
v___x_746_ = v___x_739_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push(lean_object* v_00_u03b1_749_, lean_object* v_00_u03b2_750_, lean_object* v_cmp_751_, lean_object* v_k_752_, lean_object* v_v_753_, lean_object* v_t_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_751_, v_k_752_, v_v_753_, v_t_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___redArg(lean_object* v_cmp_756_, lean_object* v_k_757_, lean_object* v_f_758_, lean_object* v_t_759_){
_start:
{
lean_object* v___x_760_; 
lean_inc_ref(v_t_759_);
lean_inc(v_k_757_);
lean_inc_ref(v_cmp_756_);
v___x_760_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_756_, v_k_757_, v_t_759_);
if (lean_obj_tag(v___x_760_) == 1)
{
lean_object* v_val_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_k_757_);
lean_dec_ref(v_cmp_756_);
v_val_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_796_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_796_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_val_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_796_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_items_765_; lean_object* v_indices_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_795_; 
v_items_765_ = lean_ctor_get(v_t_759_, 0);
v_indices_766_ = lean_ctor_get(v_t_759_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_t_759_);
if (v_isSharedCheck_795_ == 0)
{
v___x_768_ = v_t_759_;
v_isShared_769_ = v_isSharedCheck_795_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_indices_766_);
lean_inc(v_items_765_);
lean_dec(v_t_759_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_795_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v_items_765_);
v___x_771_ = lean_nat_dec_lt(v_val_761_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_773_; 
lean_del_object(v___x_763_);
lean_dec(v_val_761_);
lean_dec(v_f_758_);
if (v_isShared_769_ == 0)
{
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_items_765_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_indices_766_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
else
{
lean_object* v_v_775_; lean_object* v_fst_776_; lean_object* v_snd_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_794_; 
v_v_775_ = lean_array_fget(v_items_765_, v_val_761_);
v_fst_776_ = lean_ctor_get(v_v_775_, 0);
v_snd_777_ = lean_ctor_get(v_v_775_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_v_775_);
if (v_isSharedCheck_794_ == 0)
{
v___x_779_ = v_v_775_;
v_isShared_780_ = v_isSharedCheck_794_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_777_);
lean_inc(v_fst_776_);
lean_dec(v_v_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_794_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v_xs_x27_782_; lean_object* v___x_784_; 
v___x_781_ = lean_box(0);
v_xs_x27_782_ = lean_array_fset(v_items_765_, v_val_761_, v___x_781_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_snd_777_);
v___x_784_ = v___x_763_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_snd_777_);
v___x_784_ = v_reuseFailAlloc_793_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = lean_apply_1(v_f_758_, v___x_784_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_785_);
v___x_787_ = v___x_779_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_fst_776_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_792_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_array_fset(v_xs_x27_782_, v_val_761_, v___x_787_);
lean_dec(v_val_761_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_788_);
v___x_790_ = v___x_768_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_indices_766_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v___x_760_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_apply_1(v_f_758_, v___x_797_);
v___x_799_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_756_, v_k_757_, v___x_798_, v_t_759_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter(lean_object* v_00_u03b1_800_, lean_object* v_00_u03b2_801_, lean_object* v_cmp_802_, lean_object* v_k_803_, lean_object* v_f_804_, lean_object* v_t_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lake_Toml_RBDict_alter___redArg(v_cmp_802_, v_k_803_, v_f_804_, v_t_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert___redArg(lean_object* v_cmp_807_, lean_object* v_k_808_, lean_object* v_v_809_, lean_object* v_t_810_){
_start:
{
lean_object* v___x_811_; 
lean_inc_ref(v_t_810_);
lean_inc(v_k_808_);
lean_inc_ref(v_cmp_807_);
v___x_811_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_807_, v_k_808_, v_t_810_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; lean_object* v_items_813_; lean_object* v_indices_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_812_);
lean_dec_ref(v___x_811_);
v_items_813_ = lean_ctor_get(v_t_810_, 0);
v_indices_814_ = lean_ctor_get(v_t_810_, 1);
v___x_815_ = lean_array_get_size(v_items_813_);
v___x_816_ = lean_nat_dec_lt(v_val_812_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v_val_812_);
v___x_817_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_807_, v_k_808_, v_v_809_, v_t_810_);
return v___x_817_;
}
else
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_826_; 
lean_inc(v_indices_814_);
lean_inc_ref(v_items_813_);
lean_dec_ref(v_cmp_807_);
v_isSharedCheck_826_ = !lean_is_exclusive(v_t_810_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; lean_object* v_unused_828_; 
v_unused_827_ = lean_ctor_get(v_t_810_, 1);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_t_810_, 0);
lean_dec(v_unused_828_);
v___x_819_ = v_t_810_;
v_isShared_820_ = v_isSharedCheck_826_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_t_810_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_826_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_k_808_);
lean_ctor_set(v___x_821_, 1, v_v_809_);
v___x_822_ = lean_array_fset(v_items_813_, v_val_812_, v___x_821_);
lean_dec(v_val_812_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_822_);
v___x_824_ = v___x_819_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_indices_814_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v___x_829_; 
lean_dec(v___x_811_);
v___x_829_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_807_, v_k_808_, v_v_809_, v_t_810_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_cmp_832_, lean_object* v_k_833_, lean_object* v_v_834_, lean_object* v_t_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_832_, v_k_833_, v_v_834_, v_t_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(lean_object* v_cmp_837_, lean_object* v_as_838_, size_t v_i_839_, size_t v_stop_840_, lean_object* v_b_841_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = lean_usize_dec_eq(v_i_839_, v_stop_840_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v___x_846_; size_t v___x_847_; size_t v___x_848_; 
v___x_843_ = lean_array_uget_borrowed(v_as_838_, v_i_839_);
v_fst_844_ = lean_ctor_get(v___x_843_, 0);
v_snd_845_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_snd_845_);
lean_inc(v_fst_844_);
lean_inc_ref(v_cmp_837_);
v___x_846_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_837_, v_fst_844_, v_snd_845_, v_b_841_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_839_, v___x_847_);
v_i_839_ = v___x_848_;
v_b_841_ = v___x_846_;
goto _start;
}
else
{
lean_dec_ref(v_cmp_837_);
return v_b_841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg___boxed(lean_object* v_cmp_850_, lean_object* v_as_851_, lean_object* v_i_852_, lean_object* v_stop_853_, lean_object* v_b_854_){
_start:
{
size_t v_i_boxed_855_; size_t v_stop_boxed_856_; lean_object* v_res_857_; 
v_i_boxed_855_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_stop_boxed_856_ = lean_unbox_usize(v_stop_853_);
lean_dec(v_stop_853_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_850_, v_as_851_, v_i_boxed_855_, v_stop_boxed_856_, v_b_854_);
lean_dec_ref(v_as_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg(lean_object* v_cmp_858_, lean_object* v_self_859_, lean_object* v_other_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_array_get_size(v_other_860_);
v___x_863_ = lean_nat_dec_lt(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_dec_ref(v_cmp_858_);
return v_self_859_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = lean_nat_dec_le(v___x_862_, v___x_862_);
if (v___x_864_ == 0)
{
if (v___x_863_ == 0)
{
lean_dec_ref(v_cmp_858_);
return v_self_859_;
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_862_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_858_, v_other_860_, v___x_865_, v___x_866_, v_self_859_);
return v___x_867_;
}
}
else
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((size_t)0ULL);
v___x_869_ = lean_usize_of_nat(v___x_862_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_858_, v_other_860_, v___x_868_, v___x_869_, v_self_859_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg___boxed(lean_object* v_cmp_871_, lean_object* v_self_872_, lean_object* v_other_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_871_, v_self_872_, v_other_873_);
lean_dec_ref(v_other_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray(lean_object* v_00_u03b1_875_, lean_object* v_00_u03b2_876_, lean_object* v_cmp_877_, lean_object* v_self_878_, lean_object* v_other_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_877_, v_self_878_, v_other_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___boxed(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_cmp_883_, lean_object* v_self_884_, lean_object* v_other_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lake_Toml_RBDict_appendArray(v_00_u03b1_881_, v_00_u03b2_882_, v_cmp_883_, v_self_884_, v_other_885_);
lean_dec_ref(v_other_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_cmp_889_, lean_object* v_as_890_, size_t v_i_891_, size_t v_stop_892_, lean_object* v_b_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_889_, v_as_890_, v_i_891_, v_stop_892_, v_b_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___boxed(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_cmp_897_, lean_object* v_as_898_, lean_object* v_i_899_, lean_object* v_stop_900_, lean_object* v_b_901_){
_start:
{
size_t v_i_boxed_902_; size_t v_stop_boxed_903_; lean_object* v_res_904_; 
v_i_boxed_902_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_stop_boxed_903_ = lean_unbox_usize(v_stop_900_);
lean_dec(v_stop_900_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(v_00_u03b1_895_, v_00_u03b2_896_, v_cmp_897_, v_as_898_, v_i_boxed_902_, v_stop_boxed_903_, v_b_901_);
lean_dec_ref(v_as_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd___redArg(lean_object* v_cmp_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_appendArray___boxed), 5, 3);
lean_closure_set(v___x_906_, 0, lean_box(0));
lean_closure_set(v___x_906_, 1, lean_box(0));
lean_closure_set(v___x_906_, 2, v_cmp_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_cmp_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_appendArray___boxed), 5, 3);
lean_closure_set(v___x_910_, 0, lean_box(0));
lean_closure_set(v___x_910_, 1, lean_box(0));
lean_closure_set(v___x_910_, 2, v_cmp_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg(lean_object* v_cmp_911_, lean_object* v_self_912_, lean_object* v_other_913_){
_start:
{
lean_object* v_items_914_; lean_object* v___x_915_; 
v_items_914_ = lean_ctor_get(v_other_913_, 0);
v___x_915_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_911_, v_self_912_, v_items_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg___boxed(lean_object* v_cmp_916_, lean_object* v_self_917_, lean_object* v_other_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lake_Toml_RBDict_append___redArg(v_cmp_916_, v_self_917_, v_other_918_);
lean_dec_ref(v_other_918_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append(lean_object* v_00_u03b1_920_, lean_object* v_00_u03b2_921_, lean_object* v_cmp_922_, lean_object* v_self_923_, lean_object* v_other_924_){
_start:
{
lean_object* v_items_925_; lean_object* v___x_926_; 
v_items_925_ = lean_ctor_get(v_other_924_, 0);
v___x_926_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_922_, v_self_923_, v_items_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___boxed(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_cmp_929_, lean_object* v_self_930_, lean_object* v_other_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lake_Toml_RBDict_append(v_00_u03b1_927_, v_00_u03b2_928_, v_cmp_929_, v_self_930_, v_other_931_);
lean_dec_ref(v_other_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend___redArg(lean_object* v_cmp_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_append___boxed), 5, 3);
lean_closure_set(v___x_934_, 0, lean_box(0));
lean_closure_set(v___x_934_, 1, lean_box(0));
lean_closure_set(v___x_934_, 2, v_cmp_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_cmp_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_append___boxed), 5, 3);
lean_closure_set(v___x_938_, 0, lean_box(0));
lean_closure_set(v___x_938_, 1, lean_box(0));
lean_closure_set(v___x_938_, 2, v_cmp_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg___lam__0(lean_object* v_f_939_, lean_object* v_x_940_){
_start:
{
lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_950_; 
v_fst_941_ = lean_ctor_get(v_x_940_, 0);
v_snd_942_ = lean_ctor_get(v_x_940_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_950_ == 0)
{
v___x_944_ = v_x_940_;
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_942_);
lean_inc(v_fst_941_);
lean_dec(v_x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
lean_inc(v_fst_941_);
v___x_946_ = lean_apply_2(v_f_939_, v_fst_941_, v_snd_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_fst_941_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg(lean_object* v_f_970_, lean_object* v_t_971_){
_start:
{
lean_object* v_items_972_; lean_object* v_indices_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_985_; 
v_items_972_ = lean_ctor_get(v_t_971_, 0);
v_indices_973_ = lean_ctor_get(v_t_971_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_t_971_);
if (v_isSharedCheck_985_ == 0)
{
v___x_975_ = v_t_971_;
v_isShared_976_ = v_isSharedCheck_985_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_indices_973_);
lean_inc(v_items_972_);
lean_dec(v_t_971_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_985_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___f_977_; lean_object* v___x_978_; size_t v_sz_979_; size_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
v___f_977_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_977_, 0, v_f_970_);
v___x_978_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_sz_979_ = lean_array_size(v_items_972_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_978_, v___f_977_, v_sz_979_, v___x_980_, v_items_972_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_981_);
v___x_983_ = v___x_975_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_indices_973_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_00_u03b3_988_, lean_object* v_cmp_989_, lean_object* v_f_990_, lean_object* v_t_991_){
_start:
{
lean_object* v_items_992_; lean_object* v_indices_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1005_; 
v_items_992_ = lean_ctor_get(v_t_991_, 0);
v_indices_993_ = lean_ctor_get(v_t_991_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_t_991_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_995_ = v_t_991_;
v_isShared_996_ = v_isSharedCheck_1005_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_indices_993_);
lean_inc(v_items_992_);
lean_dec(v_t_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1005_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___f_997_; lean_object* v___x_998_; size_t v_sz_999_; size_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___f_997_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_997_, 0, v_f_990_);
v___x_998_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_sz_999_ = lean_array_size(v_items_992_);
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_998_, v___f_997_, v_sz_999_, v___x_1000_, v_items_992_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1001_);
v___x_1003_ = v___x_995_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_indices_993_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_00_u03b3_1008_, lean_object* v_cmp_1009_, lean_object* v_f_1010_, lean_object* v_t_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lake_Toml_RBDict_map(v_00_u03b1_1006_, v_00_u03b2_1007_, v_00_u03b3_1008_, v_cmp_1009_, v_f_1010_, v_t_1011_);
lean_dec_ref(v_cmp_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg___lam__0(lean_object* v_p_1013_, lean_object* v_cmp_1014_, lean_object* v_x1_1015_, lean_object* v_x2_1016_){
_start:
{
lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_fst_1017_ = lean_ctor_get(v_x2_1016_, 0);
lean_inc_n(v_fst_1017_, 2);
v_snd_1018_ = lean_ctor_get(v_x2_1016_, 1);
lean_inc_n(v_snd_1018_, 2);
lean_dec_ref(v_x2_1016_);
v___x_1019_ = lean_apply_2(v_p_1013_, v_fst_1017_, v_snd_1018_);
v___x_1020_ = lean_unbox(v___x_1019_);
if (v___x_1020_ == 0)
{
lean_dec(v_snd_1018_);
lean_dec(v_fst_1017_);
lean_dec_ref(v_cmp_1014_);
return v_x1_1015_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1014_, v_fst_1017_, v_snd_1018_, v_x1_1015_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg(lean_object* v_cmp_1022_, lean_object* v_p_1023_, lean_object* v_t_1024_){
_start:
{
lean_object* v_items_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_items_1025_ = lean_ctor_get(v_t_1024_, 0);
lean_inc_ref(v_items_1025_);
lean_dec_ref(v_t_1024_);
v___x_1026_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_1022_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_array_get_size(v_items_1025_);
v___x_1029_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1030_ = lean_nat_dec_lt(v___x_1027_, v___x_1028_);
if (v___x_1030_ == 0)
{
lean_dec_ref(v_items_1025_);
lean_dec_ref(v_p_1023_);
lean_dec_ref(v_cmp_1022_);
return v___x_1026_;
}
else
{
lean_object* v___f_1031_; uint8_t v___x_1032_; 
v___f_1031_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filter___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1031_, 0, v_p_1023_);
lean_closure_set(v___f_1031_, 1, v_cmp_1022_);
v___x_1032_ = lean_nat_dec_le(v___x_1028_, v___x_1028_);
if (v___x_1032_ == 0)
{
if (v___x_1030_ == 0)
{
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_items_1025_);
return v___x_1026_;
}
else
{
size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = ((size_t)0ULL);
v___x_1034_ = lean_usize_of_nat(v___x_1028_);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1029_, v___f_1031_, v_items_1025_, v___x_1033_, v___x_1034_, v___x_1026_);
return v___x_1035_;
}
}
else
{
size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1029_, v___f_1031_, v_items_1025_, v___x_1036_, v___x_1037_, v___x_1026_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter(lean_object* v_00_u03b1_1039_, lean_object* v_00_u03b2_1040_, lean_object* v_cmp_1041_, lean_object* v_p_1042_, lean_object* v_t_1043_){
_start:
{
lean_object* v_items_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_items_1044_ = lean_ctor_get(v_t_1043_, 0);
lean_inc_ref(v_items_1044_);
lean_dec_ref(v_t_1043_);
v___x_1045_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_1041_);
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = lean_array_get_size(v_items_1044_);
v___x_1048_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1049_ = lean_nat_dec_lt(v___x_1046_, v___x_1047_);
if (v___x_1049_ == 0)
{
lean_dec_ref(v_items_1044_);
lean_dec_ref(v_p_1042_);
lean_dec_ref(v_cmp_1041_);
return v___x_1045_;
}
else
{
lean_object* v___f_1050_; uint8_t v___x_1051_; 
v___f_1050_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filter___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1050_, 0, v_p_1042_);
lean_closure_set(v___f_1050_, 1, v_cmp_1041_);
v___x_1051_ = lean_nat_dec_le(v___x_1047_, v___x_1047_);
if (v___x_1051_ == 0)
{
if (v___x_1049_ == 0)
{
lean_dec_ref(v___f_1050_);
lean_dec_ref(v_items_1044_);
return v___x_1045_;
}
else
{
size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = lean_usize_of_nat(v___x_1047_);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1048_, v___f_1050_, v_items_1044_, v___x_1052_, v___x_1053_, v___x_1045_);
return v___x_1054_;
}
}
else
{
size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = lean_usize_of_nat(v___x_1047_);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1048_, v___f_1050_, v_items_1044_, v___x_1055_, v___x_1056_, v___x_1045_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg___lam__0(lean_object* v_f_1058_, lean_object* v_cmp_1059_, lean_object* v_x1_1060_, lean_object* v_x2_1061_){
_start:
{
lean_object* v_fst_1062_; lean_object* v_snd_1063_; lean_object* v___x_1064_; 
v_fst_1062_ = lean_ctor_get(v_x2_1061_, 0);
lean_inc_n(v_fst_1062_, 2);
v_snd_1063_ = lean_ctor_get(v_x2_1061_, 1);
lean_inc(v_snd_1063_);
lean_dec_ref(v_x2_1061_);
v___x_1064_ = lean_apply_2(v_f_1058_, v_fst_1062_, v_snd_1063_);
if (lean_obj_tag(v___x_1064_) == 1)
{
lean_object* v_val_1065_; lean_object* v___x_1066_; 
v_val_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1059_, v_fst_1062_, v_val_1065_, v_x1_1060_);
return v___x_1066_;
}
else
{
lean_dec(v___x_1064_);
lean_dec(v_fst_1062_);
lean_dec_ref(v_cmp_1059_);
return v_x1_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg(lean_object* v_cmp_1067_, lean_object* v_f_1068_, lean_object* v_t_1069_){
_start:
{
lean_object* v_items_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_items_1070_ = lean_ctor_get(v_t_1069_, 0);
lean_inc_ref(v_items_1070_);
lean_dec_ref(v_t_1069_);
v___x_1071_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_1067_);
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_array_get_size(v_items_1070_);
v___x_1074_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1075_ = lean_nat_dec_lt(v___x_1072_, v___x_1073_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_items_1070_);
lean_dec_ref(v_f_1068_);
lean_dec_ref(v_cmp_1067_);
return v___x_1071_;
}
else
{
lean_object* v___f_1076_; uint8_t v___x_1077_; 
v___f_1076_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filterMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1076_, 0, v_f_1068_);
lean_closure_set(v___f_1076_, 1, v_cmp_1067_);
v___x_1077_ = lean_nat_dec_le(v___x_1073_, v___x_1073_);
if (v___x_1077_ == 0)
{
if (v___x_1075_ == 0)
{
lean_dec_ref(v___f_1076_);
lean_dec_ref(v_items_1070_);
return v___x_1071_;
}
else
{
size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = ((size_t)0ULL);
v___x_1079_ = lean_usize_of_nat(v___x_1073_);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1074_, v___f_1076_, v_items_1070_, v___x_1078_, v___x_1079_, v___x_1071_);
return v___x_1080_;
}
}
else
{
size_t v___x_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = ((size_t)0ULL);
v___x_1082_ = lean_usize_of_nat(v___x_1073_);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1074_, v___f_1076_, v_items_1070_, v___x_1081_, v___x_1082_, v___x_1071_);
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap(lean_object* v_00_u03b1_1084_, lean_object* v_00_u03b2_1085_, lean_object* v_00_u03b3_1086_, lean_object* v_cmp_1087_, lean_object* v_f_1088_, lean_object* v_t_1089_){
_start:
{
lean_object* v_items_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_items_1090_ = lean_ctor_get(v_t_1089_, 0);
lean_inc_ref(v_items_1090_);
lean_dec_ref(v_t_1089_);
v___x_1091_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v_cmp_1087_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_array_get_size(v_items_1090_);
v___x_1094_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1095_ = lean_nat_dec_lt(v___x_1092_, v___x_1093_);
if (v___x_1095_ == 0)
{
lean_dec_ref(v_items_1090_);
lean_dec_ref(v_f_1088_);
lean_dec_ref(v_cmp_1087_);
return v___x_1091_;
}
else
{
lean_object* v___f_1096_; uint8_t v___x_1097_; 
v___f_1096_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filterMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1096_, 0, v_f_1088_);
lean_closure_set(v___f_1096_, 1, v_cmp_1087_);
v___x_1097_ = lean_nat_dec_le(v___x_1093_, v___x_1093_);
if (v___x_1097_ == 0)
{
if (v___x_1095_ == 0)
{
lean_dec_ref(v___f_1096_);
lean_dec_ref(v_items_1090_);
return v___x_1091_;
}
else
{
size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = lean_usize_of_nat(v___x_1093_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1094_, v___f_1096_, v_items_1090_, v___x_1098_, v___x_1099_, v___x_1091_);
return v___x_1100_;
}
}
else
{
size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = lean_usize_of_nat(v___x_1093_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1094_, v___f_1096_, v_items_1090_, v___x_1101_, v___x_1102_, v___x_1091_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg___lam__0(lean_object* v_f_1104_, lean_object* v_s_1105_, lean_object* v_x_1106_){
_start:
{
lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1109_; 
v_fst_1107_ = lean_ctor_get(v_x_1106_, 0);
lean_inc(v_fst_1107_);
v_snd_1108_ = lean_ctor_get(v_x_1106_, 1);
lean_inc(v_snd_1108_);
lean_dec_ref(v_x_1106_);
v___x_1109_ = lean_apply_3(v_f_1104_, v_s_1105_, v_fst_1107_, v_snd_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg(lean_object* v_inst_1110_, lean_object* v_f_1111_, lean_object* v_init_1112_, lean_object* v_t_1113_){
_start:
{
lean_object* v_items_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_items_1114_ = lean_ctor_get(v_t_1113_, 0);
lean_inc_ref(v_items_1114_);
lean_dec_ref(v_t_1113_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_array_get_size(v_items_1114_);
v___x_1117_ = lean_nat_dec_lt(v___x_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v_toApplicative_1118_; lean_object* v_toPure_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v_items_1114_);
lean_dec(v_f_1111_);
v_toApplicative_1118_ = lean_ctor_get(v_inst_1110_, 0);
lean_inc_ref(v_toApplicative_1118_);
lean_dec_ref(v_inst_1110_);
v_toPure_1119_ = lean_ctor_get(v_toApplicative_1118_, 1);
lean_inc(v_toPure_1119_);
lean_dec_ref(v_toApplicative_1118_);
v___x_1120_ = lean_apply_2(v_toPure_1119_, lean_box(0), v_init_1112_);
return v___x_1120_;
}
else
{
lean_object* v___f_1121_; uint8_t v___x_1122_; 
v___f_1121_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1121_, 0, v_f_1111_);
v___x_1122_ = lean_nat_dec_le(v___x_1116_, v___x_1116_);
if (v___x_1122_ == 0)
{
if (v___x_1117_ == 0)
{
lean_object* v_toApplicative_1123_; lean_object* v_toPure_1124_; lean_object* v___x_1125_; 
lean_dec_ref(v___f_1121_);
lean_dec_ref(v_items_1114_);
v_toApplicative_1123_ = lean_ctor_get(v_inst_1110_, 0);
lean_inc_ref(v_toApplicative_1123_);
lean_dec_ref(v_inst_1110_);
v_toPure_1124_ = lean_ctor_get(v_toApplicative_1123_, 1);
lean_inc(v_toPure_1124_);
lean_dec_ref(v_toApplicative_1123_);
v___x_1125_ = lean_apply_2(v_toPure_1124_, lean_box(0), v_init_1112_);
return v___x_1125_;
}
else
{
size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = lean_usize_of_nat(v___x_1116_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1110_, v___f_1121_, v_items_1114_, v___x_1126_, v___x_1127_, v_init_1112_);
return v___x_1128_;
}
}
else
{
size_t v___x_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = lean_usize_of_nat(v___x_1116_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1110_, v___f_1121_, v_items_1114_, v___x_1129_, v___x_1130_, v_init_1112_);
return v___x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM(lean_object* v_m_1132_, lean_object* v_00_u03c3_1133_, lean_object* v_00_u03b1_1134_, lean_object* v_00_u03b2_1135_, lean_object* v_cmp_1136_, lean_object* v_inst_1137_, lean_object* v_f_1138_, lean_object* v_init_1139_, lean_object* v_t_1140_){
_start:
{
lean_object* v_items_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_items_1141_ = lean_ctor_get(v_t_1140_, 0);
lean_inc_ref(v_items_1141_);
lean_dec_ref(v_t_1140_);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_array_get_size(v_items_1141_);
v___x_1144_ = lean_nat_dec_lt(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v_toApplicative_1145_; lean_object* v_toPure_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v_items_1141_);
lean_dec(v_f_1138_);
v_toApplicative_1145_ = lean_ctor_get(v_inst_1137_, 0);
lean_inc_ref(v_toApplicative_1145_);
lean_dec_ref(v_inst_1137_);
v_toPure_1146_ = lean_ctor_get(v_toApplicative_1145_, 1);
lean_inc(v_toPure_1146_);
lean_dec_ref(v_toApplicative_1145_);
v___x_1147_ = lean_apply_2(v_toPure_1146_, lean_box(0), v_init_1139_);
return v___x_1147_;
}
else
{
lean_object* v___f_1148_; uint8_t v___x_1149_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1148_, 0, v_f_1138_);
v___x_1149_ = lean_nat_dec_le(v___x_1143_, v___x_1143_);
if (v___x_1149_ == 0)
{
if (v___x_1144_ == 0)
{
lean_object* v_toApplicative_1150_; lean_object* v_toPure_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v___f_1148_);
lean_dec_ref(v_items_1141_);
v_toApplicative_1150_ = lean_ctor_get(v_inst_1137_, 0);
lean_inc_ref(v_toApplicative_1150_);
lean_dec_ref(v_inst_1137_);
v_toPure_1151_ = lean_ctor_get(v_toApplicative_1150_, 1);
lean_inc(v_toPure_1151_);
lean_dec_ref(v_toApplicative_1150_);
v___x_1152_ = lean_apply_2(v_toPure_1151_, lean_box(0), v_init_1139_);
return v___x_1152_;
}
else
{
size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = ((size_t)0ULL);
v___x_1154_ = lean_usize_of_nat(v___x_1143_);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1137_, v___f_1148_, v_items_1141_, v___x_1153_, v___x_1154_, v_init_1139_);
return v___x_1155_;
}
}
else
{
size_t v___x_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = ((size_t)0ULL);
v___x_1157_ = lean_usize_of_nat(v___x_1143_);
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1137_, v___f_1148_, v_items_1141_, v___x_1156_, v___x_1157_, v_init_1139_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___boxed(lean_object* v_m_1159_, lean_object* v_00_u03c3_1160_, lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_cmp_1163_, lean_object* v_inst_1164_, lean_object* v_f_1165_, lean_object* v_init_1166_, lean_object* v_t_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lake_Toml_RBDict_foldM(v_m_1159_, v_00_u03c3_1160_, v_00_u03b1_1161_, v_00_u03b2_1162_, v_cmp_1163_, v_inst_1164_, v_f_1165_, v_init_1166_, v_t_1167_);
lean_dec_ref(v_cmp_1163_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___redArg(lean_object* v_f_1169_, lean_object* v_init_1170_, lean_object* v_t_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v_items_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1172_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_items_1173_ = lean_ctor_get(v_t_1171_, 0);
lean_inc_ref(v_items_1173_);
lean_dec_ref(v_t_1171_);
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_array_get_size(v_items_1173_);
v___x_1176_ = lean_nat_dec_lt(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec_ref(v_items_1173_);
lean_dec(v_f_1169_);
return v_init_1170_;
}
else
{
lean_object* v___f_1177_; uint8_t v___x_1178_; 
v___f_1177_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1177_, 0, v_f_1169_);
v___x_1178_ = lean_nat_dec_le(v___x_1175_, v___x_1175_);
if (v___x_1178_ == 0)
{
if (v___x_1176_ == 0)
{
lean_dec_ref(v___f_1177_);
lean_dec_ref(v_items_1173_);
return v_init_1170_;
}
else
{
size_t v___x_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = lean_usize_of_nat(v___x_1175_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1172_, v___f_1177_, v_items_1173_, v___x_1179_, v___x_1180_, v_init_1170_);
return v___x_1181_;
}
}
else
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = lean_usize_of_nat(v___x_1175_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1172_, v___f_1177_, v_items_1173_, v___x_1182_, v___x_1183_, v_init_1170_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold(lean_object* v_00_u03c3_1185_, lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_cmp_1188_, lean_object* v_f_1189_, lean_object* v_init_1190_, lean_object* v_t_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v_items_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1192_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_items_1193_ = lean_ctor_get(v_t_1191_, 0);
lean_inc_ref(v_items_1193_);
lean_dec_ref(v_t_1191_);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_array_get_size(v_items_1193_);
v___x_1196_ = lean_nat_dec_lt(v___x_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_dec_ref(v_items_1193_);
lean_dec(v_f_1189_);
return v_init_1190_;
}
else
{
lean_object* v___f_1197_; uint8_t v___x_1198_; 
v___f_1197_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1197_, 0, v_f_1189_);
v___x_1198_ = lean_nat_dec_le(v___x_1195_, v___x_1195_);
if (v___x_1198_ == 0)
{
if (v___x_1196_ == 0)
{
lean_dec_ref(v___f_1197_);
lean_dec_ref(v_items_1193_);
return v_init_1190_;
}
else
{
size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((size_t)0ULL);
v___x_1200_ = lean_usize_of_nat(v___x_1195_);
v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1192_, v___f_1197_, v_items_1193_, v___x_1199_, v___x_1200_, v_init_1190_);
return v___x_1201_;
}
}
else
{
size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = lean_usize_of_nat(v___x_1195_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1192_, v___f_1197_, v_items_1193_, v___x_1202_, v___x_1203_, v_init_1190_);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___boxed(lean_object* v_00_u03c3_1205_, lean_object* v_00_u03b1_1206_, lean_object* v_00_u03b2_1207_, lean_object* v_cmp_1208_, lean_object* v_f_1209_, lean_object* v_init_1210_, lean_object* v_t_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lake_Toml_RBDict_fold(v_00_u03c3_1205_, v_00_u03b1_1206_, v_00_u03b2_1207_, v_cmp_1208_, v_f_1209_, v_init_1210_, v_t_1211_);
lean_dec_ref(v_cmp_1208_);
return v_res_1212_;
}
}
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Data_Dict(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Data_Dict(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Data_Dict(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data_Dict(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Data_Dict(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Data_Dict(builtin);
}
#ifdef __cplusplus
}
#endif
