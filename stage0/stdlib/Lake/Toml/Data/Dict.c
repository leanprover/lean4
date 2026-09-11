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
static const lean_array_object l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_Toml_instInhabitedRBDict_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_instInhabitedRBDict_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Toml_RBDict_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_RBDict_empty___redArg___closed__0 = (const lean_object*)&l_Lake_Toml_RBDict_empty___redArg___closed__0_value;
static const lean_ctor_object l_Lake_Toml_RBDict_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_RBDict_empty___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_RBDict_empty___redArg___closed__1 = (const lean_object*)&l_Lake_Toml_RBDict_empty___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_Toml_RBDict_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_RBDict_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg();
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
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__1));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_Toml_instInhabitedRBDict_default___redArg();
return v_res_9_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lake_Toml_instInhabitedRBDict_default___redArg();
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_cmp_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lake_Toml_instInhabitedRBDict_default___closed__0, &l_Lake_Toml_instInhabitedRBDict_default___closed__0_once, _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___boxed(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_cmp_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lake_Toml_instInhabitedRBDict_default(v_00_u03b1_15_, v_00_u03b2_16_, v_cmp_17_);
lean_dec_ref(v_cmp_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg(){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Lake_Toml_instInhabitedRBDict_default___closed__0, &l_Lake_Toml_instInhabitedRBDict_default___closed__0_once, _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg___boxed(lean_object* v___dummy_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lake_Toml_instInhabitedRBDict___redArg();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict(lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Lake_Toml_instInhabitedRBDict_default___closed__0, &l_Lake_Toml_instInhabitedRBDict_default___closed__0_once, _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___boxed(lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lake_Toml_instInhabitedRBDict(v_a_27_, v_a_28_, v_a_29_);
lean_dec_ref(v_a_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___redArg(){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = ((lean_object*)(l_Lake_Toml_RBDict_empty___redArg___closed__1));
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___redArg___boxed(lean_object* v___dummy_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lake_Toml_RBDict_empty___redArg();
return v_res_39_;
}
}
static lean_object* _init_l_Lake_Toml_RBDict_empty___closed__0(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_cmp_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___boxed(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_cmp_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_Toml_RBDict_empty(v_00_u03b1_45_, v_00_u03b2_46_, v_cmp_47_);
lean_dec_ref(v_cmp_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg___boxed(lean_object* v___dummy_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lake_Toml_RBDict_instEmptyCollection___redArg();
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_cmp_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___boxed(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_cmp_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lake_Toml_RBDict_instEmptyCollection(v_00_u03b1_57_, v_00_u03b2_58_, v_cmp_59_);
lean_dec_ref(v_cmp_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg(lean_object* v_capacity_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_mk_empty_array_with_capacity(v_capacity_61_);
v___x_63_ = lean_box(1);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg___boxed(lean_object* v_capacity_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_65_);
lean_dec(v_capacity_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_cmp_69_, lean_object* v_capacity_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___boxed(lean_object* v_00_u03b1_72_, lean_object* v_00_u03b2_73_, lean_object* v_cmp_74_, lean_object* v_capacity_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lake_Toml_RBDict_mkEmpty(v_00_u03b1_72_, v_00_u03b2_73_, v_cmp_74_, v_capacity_75_);
lean_dec(v_capacity_75_);
lean_dec_ref(v_cmp_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(lean_object* v_cmp_77_, lean_object* v_k_78_, lean_object* v_v_79_, lean_object* v_t_80_){
_start:
{
if (lean_obj_tag(v_t_80_) == 0)
{
lean_object* v_size_81_; lean_object* v_k_82_; lean_object* v_v_83_; lean_object* v_l_84_; lean_object* v_r_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_366_; 
v_size_81_ = lean_ctor_get(v_t_80_, 0);
v_k_82_ = lean_ctor_get(v_t_80_, 1);
v_v_83_ = lean_ctor_get(v_t_80_, 2);
v_l_84_ = lean_ctor_get(v_t_80_, 3);
v_r_85_ = lean_ctor_get(v_t_80_, 4);
v_isSharedCheck_366_ = !lean_is_exclusive(v_t_80_);
if (v_isSharedCheck_366_ == 0)
{
v___x_87_ = v_t_80_;
v_isShared_88_ = v_isSharedCheck_366_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_r_85_);
lean_inc(v_l_84_);
lean_inc(v_v_83_);
lean_inc(v_k_82_);
lean_inc(v_size_81_);
lean_dec(v_t_80_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_366_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
lean_inc_ref(v_cmp_77_);
lean_inc(v_k_82_);
lean_inc(v_k_78_);
v___x_89_ = lean_apply_2(v_cmp_77_, v_k_78_, v_k_82_);
v___x_90_ = lean_unbox(v___x_89_);
switch(v___x_90_)
{
case 0:
{
lean_object* v_impl_91_; lean_object* v___x_92_; 
lean_dec(v_size_81_);
v_impl_91_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_77_, v_k_78_, v_v_79_, v_l_84_);
v___x_92_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_85_) == 0)
{
lean_object* v_size_93_; lean_object* v_size_94_; lean_object* v_k_95_; lean_object* v_v_96_; lean_object* v_l_97_; lean_object* v_r_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_size_93_ = lean_ctor_get(v_r_85_, 0);
v_size_94_ = lean_ctor_get(v_impl_91_, 0);
lean_inc(v_size_94_);
v_k_95_ = lean_ctor_get(v_impl_91_, 1);
lean_inc(v_k_95_);
v_v_96_ = lean_ctor_get(v_impl_91_, 2);
lean_inc(v_v_96_);
v_l_97_ = lean_ctor_get(v_impl_91_, 3);
lean_inc(v_l_97_);
v_r_98_ = lean_ctor_get(v_impl_91_, 4);
lean_inc(v_r_98_);
v___x_99_ = lean_unsigned_to_nat(3u);
v___x_100_ = lean_nat_mul(v___x_99_, v_size_93_);
v___x_101_ = lean_nat_dec_lt(v___x_100_, v_size_94_);
lean_dec(v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
lean_dec(v_r_98_);
lean_dec(v_l_97_);
lean_dec(v_v_96_);
lean_dec(v_k_95_);
v___x_102_ = lean_nat_add(v___x_92_, v_size_94_);
lean_dec(v_size_94_);
v___x_103_ = lean_nat_add(v___x_102_, v_size_93_);
lean_dec(v___x_102_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 3, v_impl_91_);
lean_ctor_set(v___x_87_, 0, v___x_103_);
v___x_105_ = v___x_87_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_impl_91_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_r_85_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
else
{
lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_172_; 
v_isSharedCheck_172_ = !lean_is_exclusive(v_impl_91_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; lean_object* v_unused_174_; lean_object* v_unused_175_; lean_object* v_unused_176_; lean_object* v_unused_177_; 
v_unused_173_ = lean_ctor_get(v_impl_91_, 4);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_impl_91_, 3);
lean_dec(v_unused_174_);
v_unused_175_ = lean_ctor_get(v_impl_91_, 2);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_impl_91_, 1);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_impl_91_, 0);
lean_dec(v_unused_177_);
v___x_108_ = v_impl_91_;
v_isShared_109_ = v_isSharedCheck_172_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_impl_91_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_172_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_size_110_; lean_object* v_size_111_; lean_object* v_k_112_; lean_object* v_v_113_; lean_object* v_l_114_; lean_object* v_r_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_size_110_ = lean_ctor_get(v_l_97_, 0);
v_size_111_ = lean_ctor_get(v_r_98_, 0);
v_k_112_ = lean_ctor_get(v_r_98_, 1);
v_v_113_ = lean_ctor_get(v_r_98_, 2);
v_l_114_ = lean_ctor_get(v_r_98_, 3);
v_r_115_ = lean_ctor_get(v_r_98_, 4);
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = lean_nat_mul(v___x_116_, v_size_110_);
v___x_118_ = lean_nat_dec_lt(v_size_111_, v___x_117_);
lean_dec(v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_147_; 
lean_inc(v_r_115_);
lean_inc(v_l_114_);
lean_inc(v_v_113_);
lean_inc(v_k_112_);
v_isSharedCheck_147_ = !lean_is_exclusive(v_r_98_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; lean_object* v_unused_149_; lean_object* v_unused_150_; lean_object* v_unused_151_; lean_object* v_unused_152_; 
v_unused_148_ = lean_ctor_get(v_r_98_, 4);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v_r_98_, 3);
lean_dec(v_unused_149_);
v_unused_150_ = lean_ctor_get(v_r_98_, 2);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v_r_98_, 1);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_r_98_, 0);
lean_dec(v_unused_152_);
v___x_120_ = v_r_98_;
v_isShared_121_ = v_isSharedCheck_147_;
goto v_resetjp_119_;
}
else
{
lean_dec(v_r_98_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_147_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___x_135_; lean_object* v___y_137_; 
v___x_122_ = lean_nat_add(v___x_92_, v_size_94_);
lean_dec(v_size_94_);
v___x_123_ = lean_nat_add(v___x_122_, v_size_93_);
lean_dec(v___x_122_);
v___x_135_ = lean_nat_add(v___x_92_, v_size_110_);
if (lean_obj_tag(v_l_114_) == 0)
{
lean_object* v_size_145_; 
v_size_145_ = lean_ctor_get(v_l_114_, 0);
lean_inc(v_size_145_);
v___y_137_ = v_size_145_;
goto v___jp_136_;
}
else
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___y_137_ = v___x_146_;
goto v___jp_136_;
}
v___jp_124_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_nat_add(v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec(v___y_126_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 4, v_r_85_);
lean_ctor_set(v___x_120_, 3, v_r_115_);
lean_ctor_set(v___x_120_, 2, v_v_83_);
lean_ctor_set(v___x_120_, 1, v_k_82_);
lean_ctor_set(v___x_120_, 0, v___x_128_);
v___x_130_ = v___x_120_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_r_115_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_r_85_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 4, v___x_130_);
lean_ctor_set(v___x_108_, 3, v___y_125_);
lean_ctor_set(v___x_108_, 2, v_v_113_);
lean_ctor_set(v___x_108_, 1, v_k_112_);
lean_ctor_set(v___x_108_, 0, v___x_123_);
v___x_132_ = v___x_108_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_k_112_);
lean_ctor_set(v_reuseFailAlloc_133_, 2, v_v_113_);
lean_ctor_set(v_reuseFailAlloc_133_, 3, v___y_125_);
lean_ctor_set(v_reuseFailAlloc_133_, 4, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
v___jp_136_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_nat_add(v___x_135_, v___y_137_);
lean_dec(v___y_137_);
lean_dec(v___x_135_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v_l_114_);
lean_ctor_set(v___x_87_, 3, v_l_97_);
lean_ctor_set(v___x_87_, 2, v_v_96_);
lean_ctor_set(v___x_87_, 1, v_k_95_);
lean_ctor_set(v___x_87_, 0, v___x_138_);
v___x_140_ = v___x_87_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_l_97_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_l_114_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
v___x_141_ = lean_nat_add(v___x_92_, v_size_93_);
if (lean_obj_tag(v_r_115_) == 0)
{
lean_object* v_size_142_; 
v_size_142_ = lean_ctor_get(v_r_115_, 0);
lean_inc(v_size_142_);
v___y_125_ = v___x_140_;
v___y_126_ = v___x_141_;
v___y_127_ = v_size_142_;
goto v___jp_124_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___y_125_ = v___x_140_;
v___y_126_ = v___x_141_;
v___y_127_ = v___x_143_;
goto v___jp_124_;
}
}
}
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
lean_del_object(v___x_87_);
v___x_153_ = lean_nat_add(v___x_92_, v_size_94_);
lean_dec(v_size_94_);
v___x_154_ = lean_nat_add(v___x_153_, v_size_93_);
lean_dec(v___x_153_);
v___x_155_ = lean_nat_add(v___x_92_, v_size_93_);
v___x_156_ = lean_nat_add(v___x_155_, v_size_111_);
lean_dec(v___x_155_);
lean_inc_ref(v_r_85_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 4, v_r_85_);
lean_ctor_set(v___x_108_, 3, v_r_98_);
lean_ctor_set(v___x_108_, 2, v_v_83_);
lean_ctor_set(v___x_108_, 1, v_k_82_);
lean_ctor_set(v___x_108_, 0, v___x_156_);
v___x_158_ = v___x_108_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_r_98_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v_r_85_);
v___x_158_ = v_reuseFailAlloc_171_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_isSharedCheck_165_ = !lean_is_exclusive(v_r_85_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; lean_object* v_unused_167_; lean_object* v_unused_168_; lean_object* v_unused_169_; lean_object* v_unused_170_; 
v_unused_166_ = lean_ctor_get(v_r_85_, 4);
lean_dec(v_unused_166_);
v_unused_167_ = lean_ctor_get(v_r_85_, 3);
lean_dec(v_unused_167_);
v_unused_168_ = lean_ctor_get(v_r_85_, 2);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_r_85_, 1);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_r_85_, 0);
lean_dec(v_unused_170_);
v___x_160_ = v_r_85_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_dec(v_r_85_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 4, v___x_158_);
lean_ctor_set(v___x_160_, 3, v_l_97_);
lean_ctor_set(v___x_160_, 2, v_v_96_);
lean_ctor_set(v___x_160_, 1, v_k_95_);
lean_ctor_set(v___x_160_, 0, v___x_154_);
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_l_97_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v___x_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_178_; 
v_l_178_ = lean_ctor_get(v_impl_91_, 3);
lean_inc(v_l_178_);
if (lean_obj_tag(v_l_178_) == 0)
{
lean_object* v_r_179_; lean_object* v_k_180_; lean_object* v_v_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_192_; 
v_r_179_ = lean_ctor_get(v_impl_91_, 4);
v_k_180_ = lean_ctor_get(v_impl_91_, 1);
v_v_181_ = lean_ctor_get(v_impl_91_, 2);
v_isSharedCheck_192_ = !lean_is_exclusive(v_impl_91_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; lean_object* v_unused_194_; 
v_unused_193_ = lean_ctor_get(v_impl_91_, 3);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_impl_91_, 0);
lean_dec(v_unused_194_);
v___x_183_ = v_impl_91_;
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_r_179_);
lean_inc(v_v_181_);
lean_inc(v_k_180_);
lean_dec(v_impl_91_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_185_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_179_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 3, v_r_179_);
lean_ctor_set(v___x_183_, 2, v_v_83_);
lean_ctor_set(v___x_183_, 1, v_k_82_);
lean_ctor_set(v___x_183_, 0, v___x_92_);
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_r_179_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_r_179_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v___x_187_);
lean_ctor_set(v___x_87_, 3, v_l_178_);
lean_ctor_set(v___x_87_, 2, v_v_181_);
lean_ctor_set(v___x_87_, 1, v_k_180_);
lean_ctor_set(v___x_87_, 0, v___x_185_);
v___x_189_ = v___x_87_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_k_180_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_v_181_);
lean_ctor_set(v_reuseFailAlloc_190_, 3, v_l_178_);
lean_ctor_set(v_reuseFailAlloc_190_, 4, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_r_195_; 
v_r_195_ = lean_ctor_get(v_impl_91_, 4);
lean_inc(v_r_195_);
if (lean_obj_tag(v_r_195_) == 0)
{
lean_object* v_k_196_; lean_object* v_v_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_220_; 
v_k_196_ = lean_ctor_get(v_impl_91_, 1);
v_v_197_ = lean_ctor_get(v_impl_91_, 2);
v_isSharedCheck_220_ = !lean_is_exclusive(v_impl_91_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; lean_object* v_unused_222_; lean_object* v_unused_223_; 
v_unused_221_ = lean_ctor_get(v_impl_91_, 4);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_impl_91_, 3);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_impl_91_, 0);
lean_dec(v_unused_223_);
v___x_199_ = v_impl_91_;
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_v_197_);
lean_inc(v_k_196_);
lean_dec(v_impl_91_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_k_201_; lean_object* v_v_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_216_; 
v_k_201_ = lean_ctor_get(v_r_195_, 1);
v_v_202_ = lean_ctor_get(v_r_195_, 2);
v_isSharedCheck_216_ = !lean_is_exclusive(v_r_195_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; 
v_unused_217_ = lean_ctor_get(v_r_195_, 4);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_r_195_, 3);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_r_195_, 0);
lean_dec(v_unused_219_);
v___x_204_ = v_r_195_;
v_isShared_205_ = v_isSharedCheck_216_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_v_202_);
lean_inc(v_k_201_);
lean_dec(v_r_195_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_216_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(3u);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 4, v_l_178_);
lean_ctor_set(v___x_204_, 3, v_l_178_);
lean_ctor_set(v___x_204_, 2, v_v_197_);
lean_ctor_set(v___x_204_, 1, v_k_196_);
lean_ctor_set(v___x_204_, 0, v___x_92_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_k_196_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v_v_197_);
lean_ctor_set(v_reuseFailAlloc_215_, 3, v_l_178_);
lean_ctor_set(v_reuseFailAlloc_215_, 4, v_l_178_);
v___x_208_ = v_reuseFailAlloc_215_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 4, v_l_178_);
lean_ctor_set(v___x_199_, 2, v_v_83_);
lean_ctor_set(v___x_199_, 1, v_k_82_);
lean_ctor_set(v___x_199_, 0, v___x_92_);
v___x_210_ = v___x_199_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_l_178_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_l_178_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v___x_210_);
lean_ctor_set(v___x_87_, 3, v___x_208_);
lean_ctor_set(v___x_87_, 2, v_v_202_);
lean_ctor_set(v___x_87_, 1, v_k_201_);
lean_ctor_set(v___x_87_, 0, v___x_206_);
v___x_212_ = v___x_87_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_k_201_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_v_202_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_unsigned_to_nat(2u);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v_r_195_);
lean_ctor_set(v___x_87_, 3, v_impl_91_);
lean_ctor_set(v___x_87_, 0, v___x_224_);
v___x_226_ = v___x_87_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_impl_91_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_r_195_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
case 1:
{
lean_object* v___x_229_; 
lean_dec(v_v_83_);
lean_dec(v_k_82_);
lean_dec_ref(v_cmp_77_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 2, v_v_79_);
lean_ctor_set(v___x_87_, 1, v_k_78_);
v___x_229_ = v___x_87_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_size_81_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_k_78_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_v_79_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_l_84_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_r_85_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
default: 
{
lean_object* v_impl_231_; lean_object* v___x_232_; 
lean_dec(v_size_81_);
v_impl_231_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_77_, v_k_78_, v_v_79_, v_r_85_);
v___x_232_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_84_) == 0)
{
lean_object* v_size_233_; lean_object* v_size_234_; lean_object* v_k_235_; lean_object* v_v_236_; lean_object* v_l_237_; lean_object* v_r_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_size_233_ = lean_ctor_get(v_l_84_, 0);
v_size_234_ = lean_ctor_get(v_impl_231_, 0);
lean_inc(v_size_234_);
v_k_235_ = lean_ctor_get(v_impl_231_, 1);
lean_inc(v_k_235_);
v_v_236_ = lean_ctor_get(v_impl_231_, 2);
lean_inc(v_v_236_);
v_l_237_ = lean_ctor_get(v_impl_231_, 3);
lean_inc(v_l_237_);
v_r_238_ = lean_ctor_get(v_impl_231_, 4);
lean_inc(v_r_238_);
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = lean_nat_mul(v___x_239_, v_size_233_);
v___x_241_ = lean_nat_dec_lt(v___x_240_, v_size_234_);
lean_dec(v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
lean_dec(v_r_238_);
lean_dec(v_l_237_);
lean_dec(v_v_236_);
lean_dec(v_k_235_);
v___x_242_ = lean_nat_add(v___x_232_, v_size_233_);
v___x_243_ = lean_nat_add(v___x_242_, v_size_234_);
lean_dec(v_size_234_);
lean_dec(v___x_242_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v_impl_231_);
lean_ctor_set(v___x_87_, 0, v___x_243_);
v___x_245_ = v___x_87_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_l_84_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_impl_231_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
else
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_310_; 
v_isSharedCheck_310_ = !lean_is_exclusive(v_impl_231_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; lean_object* v_unused_312_; lean_object* v_unused_313_; lean_object* v_unused_314_; lean_object* v_unused_315_; 
v_unused_311_ = lean_ctor_get(v_impl_231_, 4);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_impl_231_, 3);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_impl_231_, 2);
lean_dec(v_unused_313_);
v_unused_314_ = lean_ctor_get(v_impl_231_, 1);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_impl_231_, 0);
lean_dec(v_unused_315_);
v___x_248_ = v_impl_231_;
v_isShared_249_ = v_isSharedCheck_310_;
goto v_resetjp_247_;
}
else
{
lean_dec(v_impl_231_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_310_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v_size_250_; lean_object* v_k_251_; lean_object* v_v_252_; lean_object* v_l_253_; lean_object* v_r_254_; lean_object* v_size_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_size_250_ = lean_ctor_get(v_l_237_, 0);
v_k_251_ = lean_ctor_get(v_l_237_, 1);
v_v_252_ = lean_ctor_get(v_l_237_, 2);
v_l_253_ = lean_ctor_get(v_l_237_, 3);
v_r_254_ = lean_ctor_get(v_l_237_, 4);
v_size_255_ = lean_ctor_get(v_r_238_, 0);
v___x_256_ = lean_unsigned_to_nat(2u);
v___x_257_ = lean_nat_mul(v___x_256_, v_size_255_);
v___x_258_ = lean_nat_dec_lt(v_size_250_, v___x_257_);
lean_dec(v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_286_; 
lean_inc(v_r_254_);
lean_inc(v_l_253_);
lean_inc(v_v_252_);
lean_inc(v_k_251_);
v_isSharedCheck_286_ = !lean_is_exclusive(v_l_237_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; 
v_unused_287_ = lean_ctor_get(v_l_237_, 4);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_l_237_, 3);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_l_237_, 2);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_l_237_, 1);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_l_237_, 0);
lean_dec(v_unused_291_);
v___x_260_ = v_l_237_;
v_isShared_261_ = v_isSharedCheck_286_;
goto v_resetjp_259_;
}
else
{
lean_dec(v_l_237_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_286_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_276_; 
v___x_262_ = lean_nat_add(v___x_232_, v_size_233_);
v___x_263_ = lean_nat_add(v___x_262_, v_size_234_);
lean_dec(v_size_234_);
if (lean_obj_tag(v_l_253_) == 0)
{
lean_object* v_size_284_; 
v_size_284_ = lean_ctor_get(v_l_253_, 0);
lean_inc(v_size_284_);
v___y_276_ = v_size_284_;
goto v___jp_275_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___y_276_ = v___x_285_;
goto v___jp_275_;
}
v___jp_264_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_nat_add(v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec(v___y_266_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 4, v_r_238_);
lean_ctor_set(v___x_260_, 3, v_r_254_);
lean_ctor_set(v___x_260_, 2, v_v_236_);
lean_ctor_set(v___x_260_, 1, v_k_235_);
lean_ctor_set(v___x_260_, 0, v___x_268_);
v___x_270_ = v___x_260_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_k_235_);
lean_ctor_set(v_reuseFailAlloc_274_, 2, v_v_236_);
lean_ctor_set(v_reuseFailAlloc_274_, 3, v_r_254_);
lean_ctor_set(v_reuseFailAlloc_274_, 4, v_r_238_);
v___x_270_ = v_reuseFailAlloc_274_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_272_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v___x_270_);
lean_ctor_set(v___x_248_, 3, v___y_265_);
lean_ctor_set(v___x_248_, 2, v_v_252_);
lean_ctor_set(v___x_248_, 1, v_k_251_);
lean_ctor_set(v___x_248_, 0, v___x_263_);
v___x_272_ = v___x_248_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_k_251_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_v_252_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v___y_265_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_nat_add(v___x_262_, v___y_276_);
lean_dec(v___y_276_);
lean_dec(v___x_262_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v_l_253_);
lean_ctor_set(v___x_87_, 0, v___x_277_);
v___x_279_ = v___x_87_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_l_84_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_l_253_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; 
v___x_280_ = lean_nat_add(v___x_232_, v_size_255_);
if (lean_obj_tag(v_r_254_) == 0)
{
lean_object* v_size_281_; 
v_size_281_ = lean_ctor_get(v_r_254_, 0);
lean_inc(v_size_281_);
v___y_265_ = v___x_279_;
v___y_266_ = v___x_280_;
v___y_267_ = v_size_281_;
goto v___jp_264_;
}
else
{
lean_object* v___x_282_; 
v___x_282_ = lean_unsigned_to_nat(0u);
v___y_265_ = v___x_279_;
v___y_266_ = v___x_280_;
v___y_267_ = v___x_282_;
goto v___jp_264_;
}
}
}
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
lean_del_object(v___x_87_);
v___x_292_ = lean_nat_add(v___x_232_, v_size_233_);
v___x_293_ = lean_nat_add(v___x_292_, v_size_234_);
lean_dec(v_size_234_);
v___x_294_ = lean_nat_add(v___x_292_, v_size_250_);
lean_dec(v___x_292_);
lean_inc_ref(v_l_84_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v_l_237_);
lean_ctor_set(v___x_248_, 3, v_l_84_);
lean_ctor_set(v___x_248_, 2, v_v_83_);
lean_ctor_set(v___x_248_, 1, v_k_82_);
lean_ctor_set(v___x_248_, 0, v___x_294_);
v___x_296_ = v___x_248_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_l_84_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_l_237_);
v___x_296_ = v_reuseFailAlloc_309_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_isSharedCheck_303_ = !lean_is_exclusive(v_l_84_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; 
v_unused_304_ = lean_ctor_get(v_l_84_, 4);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_l_84_, 3);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_l_84_, 2);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_l_84_, 1);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_l_84_, 0);
lean_dec(v_unused_308_);
v___x_298_ = v_l_84_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_l_84_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 4, v_r_238_);
lean_ctor_set(v___x_298_, 3, v___x_296_);
lean_ctor_set(v___x_298_, 2, v_v_236_);
lean_ctor_set(v___x_298_, 1, v_k_235_);
lean_ctor_set(v___x_298_, 0, v___x_293_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_k_235_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_v_236_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_r_238_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_316_; 
v_l_316_ = lean_ctor_get(v_impl_231_, 3);
lean_inc(v_l_316_);
if (lean_obj_tag(v_l_316_) == 0)
{
lean_object* v_r_317_; lean_object* v_k_318_; lean_object* v_v_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_342_; 
v_r_317_ = lean_ctor_get(v_impl_231_, 4);
v_k_318_ = lean_ctor_get(v_impl_231_, 1);
v_v_319_ = lean_ctor_get(v_impl_231_, 2);
v_isSharedCheck_342_ = !lean_is_exclusive(v_impl_231_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; 
v_unused_343_ = lean_ctor_get(v_impl_231_, 3);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_impl_231_, 0);
lean_dec(v_unused_344_);
v___x_321_ = v_impl_231_;
v_isShared_322_ = v_isSharedCheck_342_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_r_317_);
lean_inc(v_v_319_);
lean_inc(v_k_318_);
lean_dec(v_impl_231_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_342_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_338_; 
v_k_323_ = lean_ctor_get(v_l_316_, 1);
v_v_324_ = lean_ctor_get(v_l_316_, 2);
v_isSharedCheck_338_ = !lean_is_exclusive(v_l_316_);
if (v_isSharedCheck_338_ == 0)
{
lean_object* v_unused_339_; lean_object* v_unused_340_; lean_object* v_unused_341_; 
v_unused_339_ = lean_ctor_get(v_l_316_, 4);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_l_316_, 3);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_l_316_, 0);
lean_dec(v_unused_341_);
v___x_326_ = v_l_316_;
v_isShared_327_ = v_isSharedCheck_338_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_v_324_);
lean_inc(v_k_323_);
lean_dec(v_l_316_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_338_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_317_, 2);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 4, v_r_317_);
lean_ctor_set(v___x_326_, 3, v_r_317_);
lean_ctor_set(v___x_326_, 2, v_v_83_);
lean_ctor_set(v___x_326_, 1, v_k_82_);
lean_ctor_set(v___x_326_, 0, v___x_232_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_r_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_r_317_);
v___x_330_ = v_reuseFailAlloc_337_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
lean_inc(v_r_317_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 3, v_r_317_);
lean_ctor_set(v___x_321_, 0, v___x_232_);
v___x_332_ = v___x_321_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_k_318_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_v_319_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_r_317_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_r_317_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_334_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v___x_332_);
lean_ctor_set(v___x_87_, 3, v___x_330_);
lean_ctor_set(v___x_87_, 2, v_v_324_);
lean_ctor_set(v___x_87_, 1, v_k_323_);
lean_ctor_set(v___x_87_, 0, v___x_328_);
v___x_334_ = v___x_87_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_k_323_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_v_324_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
}
else
{
lean_object* v_r_345_; 
v_r_345_ = lean_ctor_get(v_impl_231_, 4);
lean_inc(v_r_345_);
if (lean_obj_tag(v_r_345_) == 0)
{
lean_object* v_k_346_; lean_object* v_v_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_358_; 
v_k_346_ = lean_ctor_get(v_impl_231_, 1);
v_v_347_ = lean_ctor_get(v_impl_231_, 2);
v_isSharedCheck_358_ = !lean_is_exclusive(v_impl_231_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; lean_object* v_unused_360_; lean_object* v_unused_361_; 
v_unused_359_ = lean_ctor_get(v_impl_231_, 4);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v_impl_231_, 3);
lean_dec(v_unused_360_);
v_unused_361_ = lean_ctor_get(v_impl_231_, 0);
lean_dec(v_unused_361_);
v___x_349_ = v_impl_231_;
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_v_347_);
lean_inc(v_k_346_);
lean_dec(v_impl_231_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_unsigned_to_nat(3u);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 4, v_l_316_);
lean_ctor_set(v___x_349_, 2, v_v_83_);
lean_ctor_set(v___x_349_, 1, v_k_82_);
lean_ctor_set(v___x_349_, 0, v___x_232_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_l_316_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_l_316_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v_r_345_);
lean_ctor_set(v___x_87_, 3, v___x_353_);
lean_ctor_set(v___x_87_, 2, v_v_347_);
lean_ctor_set(v___x_87_, 1, v_k_346_);
lean_ctor_set(v___x_87_, 0, v___x_351_);
v___x_355_ = v___x_87_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_k_346_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_v_347_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v_r_345_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(2u);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v_impl_231_);
lean_ctor_set(v___x_87_, 3, v_r_345_);
lean_ctor_set(v___x_87_, 0, v___x_362_);
v___x_364_ = v___x_87_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_r_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_impl_231_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
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
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec_ref(v_cmp_77_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_k_78_);
lean_ctor_set(v___x_368_, 2, v_v_79_);
lean_ctor_set(v___x_368_, 3, v_t_80_);
lean_ctor_set(v___x_368_, 4, v_t_80_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(lean_object* v_items_369_, lean_object* v_cmp_370_, lean_object* v_n_371_, lean_object* v_j_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_zero_374_; uint8_t v_isZero_375_; 
v_zero_374_ = lean_unsigned_to_nat(0u);
v_isZero_375_ = lean_nat_dec_eq(v_j_372_, v_zero_374_);
if (v_isZero_375_ == 1)
{
lean_dec(v_j_372_);
lean_dec_ref(v_cmp_370_);
return v_a_373_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_fst_378_; lean_object* v_one_379_; lean_object* v_n_380_; lean_object* v___x_381_; 
v___x_376_ = lean_nat_sub(v_n_371_, v_j_372_);
v___x_377_ = lean_array_fget_borrowed(v_items_369_, v___x_376_);
v_fst_378_ = lean_ctor_get(v___x_377_, 0);
v_one_379_ = lean_unsigned_to_nat(1u);
v_n_380_ = lean_nat_sub(v_j_372_, v_one_379_);
lean_dec(v_j_372_);
lean_inc(v_fst_378_);
lean_inc_ref(v_cmp_370_);
v___x_381_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_370_, v_fst_378_, v___x_376_, v_a_373_);
v_j_372_ = v_n_380_;
v_a_373_ = v___x_381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg___boxed(lean_object* v_items_383_, lean_object* v_cmp_384_, lean_object* v_n_385_, lean_object* v_j_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_383_, v_cmp_384_, v_n_385_, v_j_386_, v_a_387_);
lean_dec(v_n_385_);
lean_dec_ref(v_items_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray___redArg(lean_object* v_cmp_389_, lean_object* v_items_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_indices_393_; lean_object* v___x_394_; 
v___x_391_ = lean_array_get_size(v_items_390_);
v___x_392_ = lean_box(1);
v_indices_393_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_390_, v_cmp_389_, v___x_391_, v___x_391_, v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v_items_390_);
lean_ctor_set(v___x_394_, 1, v_indices_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_cmp_397_, lean_object* v_items_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lake_Toml_RBDict_ofArray___redArg(v_cmp_397_, v_items_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0(lean_object* v_00_u03b1_400_, lean_object* v_cmp_401_, lean_object* v_00_u03b2_402_, lean_object* v_k_403_, lean_object* v_v_404_, lean_object* v_t_405_, lean_object* v_hl_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_401_, v_k_403_, v_v_404_, v_t_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(lean_object* v_00_u03b1_408_, lean_object* v_00_u03b2_409_, lean_object* v_items_410_, lean_object* v_cmp_411_, lean_object* v_n_412_, lean_object* v_j_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_410_, v_cmp_411_, v_n_412_, v_j_413_, v_a_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___boxed(lean_object* v_00_u03b1_417_, lean_object* v_00_u03b2_418_, lean_object* v_items_419_, lean_object* v_cmp_420_, lean_object* v_n_421_, lean_object* v_j_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(v_00_u03b1_417_, v_00_u03b2_418_, v_items_419_, v_cmp_420_, v_n_421_, v_j_422_, v_a_423_, v_a_424_);
lean_dec(v_n_421_);
lean_dec_ref(v_items_419_);
return v_res_425_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___redArg(lean_object* v_inst_426_, lean_object* v_self_427_, lean_object* v_other_428_){
_start:
{
lean_object* v_items_429_; lean_object* v_items_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_items_429_ = lean_ctor_get(v_self_427_, 0);
v_items_430_ = lean_ctor_get(v_other_428_, 0);
v___x_431_ = lean_array_get_size(v_items_429_);
v___x_432_ = lean_array_get_size(v_items_430_);
v___x_433_ = lean_nat_dec_eq(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec_ref(v_inst_426_);
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = l_Array_isEqvAux___redArg(v_items_429_, v_items_430_, v_inst_426_, v___x_431_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___redArg___boxed(lean_object* v_inst_435_, lean_object* v_self_436_, lean_object* v_other_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_435_, v_self_436_, v_other_437_);
lean_dec_ref(v_other_437_);
lean_dec_ref(v_self_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_cmp_442_, lean_object* v_inst_443_, lean_object* v_self_444_, lean_object* v_other_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_443_, v_self_444_, v_other_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___boxed(lean_object* v_00_u03b1_447_, lean_object* v_00_u03b2_448_, lean_object* v_cmp_449_, lean_object* v_inst_450_, lean_object* v_self_451_, lean_object* v_other_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Lake_Toml_RBDict_beq(v_00_u03b1_447_, v_00_u03b2_448_, v_cmp_449_, v_inst_450_, v_self_451_, v_other_452_);
lean_dec_ref(v_other_452_);
lean_dec_ref(v_self_451_);
lean_dec_ref(v_cmp_449_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd___redArg(lean_object* v_cmp_455_, lean_object* v_inst_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_beq___boxed), 6, 4);
lean_closure_set(v___x_457_, 0, lean_box(0));
lean_closure_set(v___x_457_, 1, lean_box(0));
lean_closure_set(v___x_457_, 2, v_cmp_455_);
lean_closure_set(v___x_457_, 3, v_inst_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_cmp_460_, lean_object* v_inst_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_beq___boxed), 6, 4);
lean_closure_set(v___x_462_, 0, lean_box(0));
lean_closure_set(v___x_462_, 1, lean_box(0));
lean_closure_set(v___x_462_, 2, v_cmp_460_);
lean_closure_set(v___x_462_, 3, v_inst_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg(lean_object* v_t_463_){
_start:
{
lean_object* v_items_464_; lean_object* v___x_465_; 
v_items_464_ = lean_ctor_get(v_t_463_, 0);
v___x_465_ = lean_array_get_size(v_items_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg___boxed(lean_object* v_t_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lake_Toml_RBDict_size___redArg(v_t_466_);
lean_dec_ref(v_t_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_cmp_470_, lean_object* v_t_471_){
_start:
{
lean_object* v_items_472_; lean_object* v___x_473_; 
v_items_472_ = lean_ctor_get(v_t_471_, 0);
v___x_473_ = lean_array_get_size(v_items_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___boxed(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_cmp_476_, lean_object* v_t_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lake_Toml_RBDict_size(v_00_u03b1_474_, v_00_u03b2_475_, v_cmp_476_, v_t_477_);
lean_dec_ref(v_t_477_);
lean_dec_ref(v_cmp_476_);
return v_res_478_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_isEmpty___redArg(lean_object* v_t_479_){
_start:
{
lean_object* v_items_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_items_480_ = lean_ctor_get(v_t_479_, 0);
v___x_481_ = lean_array_get_size(v_items_480_);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_nat_dec_eq(v___x_481_, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___redArg___boxed(lean_object* v_t_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Lake_Toml_RBDict_isEmpty___redArg(v_t_484_);
lean_dec_ref(v_t_484_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_isEmpty(lean_object* v_00_u03b1_487_, lean_object* v_00_u03b2_488_, lean_object* v_cmp_489_, lean_object* v_t_490_){
_start:
{
lean_object* v_items_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_items_491_ = lean_ctor_get(v_t_490_, 0);
v___x_492_ = lean_array_get_size(v_items_491_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_nat_dec_eq(v___x_492_, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___boxed(lean_object* v_00_u03b1_495_, lean_object* v_00_u03b2_496_, lean_object* v_cmp_497_, lean_object* v_t_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Lake_Toml_RBDict_isEmpty(v_00_u03b1_495_, v_00_u03b2_496_, v_cmp_497_, v_t_498_);
lean_dec_ref(v_t_498_);
lean_dec_ref(v_cmp_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(size_t v_sz_501_, size_t v_i_502_, lean_object* v_bs_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_504_ == 0)
{
return v_bs_503_;
}
else
{
lean_object* v_v_505_; lean_object* v_fst_506_; lean_object* v___x_507_; lean_object* v_bs_x27_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_v_505_ = lean_array_uget_borrowed(v_bs_503_, v_i_502_);
v_fst_506_ = lean_ctor_get(v_v_505_, 0);
lean_inc(v_fst_506_);
v___x_507_ = lean_unsigned_to_nat(0u);
v_bs_x27_508_ = lean_array_uset(v_bs_503_, v_i_502_, v___x_507_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_502_, v___x_509_);
v___x_511_ = lean_array_uset(v_bs_x27_508_, v_i_502_, v_fst_506_);
v_i_502_ = v___x_510_;
v_bs_503_ = v___x_511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg___boxed(lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_bs_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_boxed_516_, v_i_boxed_517_, v_bs_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___redArg(lean_object* v_t_519_){
_start:
{
lean_object* v_items_520_; size_t v_sz_521_; size_t v___x_522_; lean_object* v___x_523_; 
v_items_520_ = lean_ctor_get(v_t_519_, 0);
lean_inc_ref(v_items_520_);
lean_dec_ref(v_t_519_);
v_sz_521_ = lean_array_size(v_items_520_);
v___x_522_ = ((size_t)0ULL);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_521_, v___x_522_, v_items_520_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_cmp_526_, lean_object* v_t_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lake_Toml_RBDict_keys___redArg(v_t_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___boxed(lean_object* v_00_u03b1_529_, lean_object* v_00_u03b2_530_, lean_object* v_cmp_531_, lean_object* v_t_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lake_Toml_RBDict_keys(v_00_u03b1_529_, v_00_u03b2_530_, v_cmp_531_, v_t_532_);
lean_dec_ref(v_cmp_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(lean_object* v_00_u03b1_534_, lean_object* v_00_u03b2_535_, size_t v_sz_536_, size_t v_i_537_, lean_object* v_bs_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_536_, v_i_537_, v_bs_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___boxed(lean_object* v_00_u03b1_540_, lean_object* v_00_u03b2_541_, lean_object* v_sz_542_, lean_object* v_i_543_, lean_object* v_bs_544_){
_start:
{
size_t v_sz_boxed_545_; size_t v_i_boxed_546_; lean_object* v_res_547_; 
v_sz_boxed_545_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v_i_boxed_546_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(v_00_u03b1_540_, v_00_u03b2_541_, v_sz_boxed_545_, v_i_boxed_546_, v_bs_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(size_t v_sz_548_, size_t v_i_549_, lean_object* v_bs_550_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = lean_usize_dec_lt(v_i_549_, v_sz_548_);
if (v___x_551_ == 0)
{
return v_bs_550_;
}
else
{
lean_object* v_v_552_; lean_object* v_snd_553_; lean_object* v___x_554_; lean_object* v_bs_x27_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v_v_552_ = lean_array_uget_borrowed(v_bs_550_, v_i_549_);
v_snd_553_ = lean_ctor_get(v_v_552_, 1);
lean_inc(v_snd_553_);
v___x_554_ = lean_unsigned_to_nat(0u);
v_bs_x27_555_ = lean_array_uset(v_bs_550_, v_i_549_, v___x_554_);
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_549_, v___x_556_);
v___x_558_ = lean_array_uset(v_bs_x27_555_, v_i_549_, v_snd_553_);
v_i_549_ = v___x_557_;
v_bs_550_ = v___x_558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg___boxed(lean_object* v_sz_560_, lean_object* v_i_561_, lean_object* v_bs_562_){
_start:
{
size_t v_sz_boxed_563_; size_t v_i_boxed_564_; lean_object* v_res_565_; 
v_sz_boxed_563_ = lean_unbox_usize(v_sz_560_);
lean_dec(v_sz_560_);
v_i_boxed_564_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_boxed_563_, v_i_boxed_564_, v_bs_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___redArg(lean_object* v_t_566_){
_start:
{
lean_object* v_items_567_; size_t v_sz_568_; size_t v___x_569_; lean_object* v___x_570_; 
v_items_567_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_items_567_);
lean_dec_ref(v_t_566_);
v_sz_568_ = lean_array_size(v_items_567_);
v___x_569_ = ((size_t)0ULL);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_568_, v___x_569_, v_items_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values(lean_object* v_00_u03b1_571_, lean_object* v_00_u03b2_572_, lean_object* v_cmp_573_, lean_object* v_t_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lake_Toml_RBDict_values___redArg(v_t_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___boxed(lean_object* v_00_u03b1_576_, lean_object* v_00_u03b2_577_, lean_object* v_cmp_578_, lean_object* v_t_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lake_Toml_RBDict_values(v_00_u03b1_576_, v_00_u03b2_577_, v_cmp_578_, v_t_579_);
lean_dec_ref(v_cmp_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, size_t v_sz_583_, size_t v_i_584_, lean_object* v_bs_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_583_, v_i_584_, v_bs_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___boxed(lean_object* v_00_u03b1_587_, lean_object* v_00_u03b2_588_, lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_bs_591_){
_start:
{
size_t v_sz_boxed_592_; size_t v_i_boxed_593_; lean_object* v_res_594_; 
v_sz_boxed_592_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_593_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(v_00_u03b1_587_, v_00_u03b2_588_, v_sz_boxed_592_, v_i_boxed_593_, v_bs_591_);
return v_res_594_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(lean_object* v_cmp_595_, lean_object* v_k_596_, lean_object* v_t_597_){
_start:
{
if (lean_obj_tag(v_t_597_) == 0)
{
lean_object* v_k_598_; lean_object* v_l_599_; lean_object* v_r_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_k_598_ = lean_ctor_get(v_t_597_, 1);
lean_inc(v_k_598_);
v_l_599_ = lean_ctor_get(v_t_597_, 3);
lean_inc(v_l_599_);
v_r_600_ = lean_ctor_get(v_t_597_, 4);
lean_inc(v_r_600_);
lean_dec_ref_known(v_t_597_, 5);
lean_inc_ref(v_cmp_595_);
lean_inc(v_k_596_);
v___x_601_ = lean_apply_2(v_cmp_595_, v_k_596_, v_k_598_);
v___x_602_ = lean_unbox(v___x_601_);
switch(v___x_602_)
{
case 0:
{
lean_dec(v_r_600_);
v_t_597_ = v_l_599_;
goto _start;
}
case 1:
{
uint8_t v___x_604_; 
lean_dec(v_r_600_);
lean_dec(v_l_599_);
lean_dec(v_k_596_);
lean_dec_ref(v_cmp_595_);
v___x_604_ = 1;
return v___x_604_;
}
default: 
{
lean_dec(v_l_599_);
v_t_597_ = v_r_600_;
goto _start;
}
}
}
else
{
uint8_t v___x_606_; 
lean_dec(v_k_596_);
lean_dec_ref(v_cmp_595_);
v___x_606_ = 0;
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg___boxed(lean_object* v_cmp_607_, lean_object* v_k_608_, lean_object* v_t_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_607_, v_k_608_, v_t_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object* v_cmp_612_, lean_object* v_k_613_, lean_object* v_t_614_){
_start:
{
lean_object* v_indices_615_; uint8_t v___x_616_; 
v_indices_615_ = lean_ctor_get(v_t_614_, 1);
lean_inc(v_indices_615_);
lean_dec_ref(v_t_614_);
v___x_616_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_612_, v_k_613_, v_indices_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___redArg___boxed(lean_object* v_cmp_617_, lean_object* v_k_618_, lean_object* v_t_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_617_, v_k_618_, v_t_619_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_contains(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_cmp_624_, lean_object* v_k_625_, lean_object* v_t_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_624_, v_k_625_, v_t_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___boxed(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_cmp_630_, lean_object* v_k_631_, lean_object* v_t_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Lake_Toml_RBDict_contains(v_00_u03b1_628_, v_00_u03b2_629_, v_cmp_630_, v_k_631_, v_t_632_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(lean_object* v_00_u03b1_635_, lean_object* v_cmp_636_, lean_object* v_00_u03b2_637_, lean_object* v_k_638_, lean_object* v_t_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_636_, v_k_638_, v_t_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___boxed(lean_object* v_00_u03b1_641_, lean_object* v_cmp_642_, lean_object* v_00_u03b2_643_, lean_object* v_k_644_, lean_object* v_t_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(v_00_u03b1_641_, v_cmp_642_, v_00_u03b2_643_, v_k_644_, v_t_645_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(lean_object* v_cmp_648_, lean_object* v_t_649_, lean_object* v_k_650_){
_start:
{
if (lean_obj_tag(v_t_649_) == 0)
{
lean_object* v_k_651_; lean_object* v_v_652_; lean_object* v_l_653_; lean_object* v_r_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_k_651_ = lean_ctor_get(v_t_649_, 1);
lean_inc(v_k_651_);
v_v_652_ = lean_ctor_get(v_t_649_, 2);
lean_inc(v_v_652_);
v_l_653_ = lean_ctor_get(v_t_649_, 3);
lean_inc(v_l_653_);
v_r_654_ = lean_ctor_get(v_t_649_, 4);
lean_inc(v_r_654_);
lean_dec_ref_known(v_t_649_, 5);
lean_inc_ref(v_cmp_648_);
lean_inc(v_k_650_);
v___x_655_ = lean_apply_2(v_cmp_648_, v_k_650_, v_k_651_);
v___x_656_ = lean_unbox(v___x_655_);
switch(v___x_656_)
{
case 0:
{
lean_dec(v_r_654_);
lean_dec(v_v_652_);
v_t_649_ = v_l_653_;
goto _start;
}
case 1:
{
lean_object* v___x_658_; 
lean_dec(v_r_654_);
lean_dec(v_l_653_);
lean_dec(v_k_650_);
lean_dec_ref(v_cmp_648_);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v_v_652_);
return v___x_658_;
}
default: 
{
lean_dec(v_l_653_);
lean_dec(v_v_652_);
v_t_649_ = v_r_654_;
goto _start;
}
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v_k_650_);
lean_dec_ref(v_cmp_648_);
v___x_660_ = lean_box(0);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f___redArg(lean_object* v_cmp_661_, lean_object* v_k_662_, lean_object* v_t_663_){
_start:
{
lean_object* v_items_664_; lean_object* v_indices_665_; lean_object* v___x_666_; 
v_items_664_ = lean_ctor_get(v_t_663_, 0);
lean_inc_ref(v_items_664_);
v_indices_665_ = lean_ctor_get(v_t_663_, 1);
lean_inc(v_indices_665_);
lean_dec_ref(v_t_663_);
v___x_666_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_661_, v_indices_665_, v_k_662_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_items_664_);
v___x_667_ = lean_box(0);
return v___x_667_;
}
else
{
lean_object* v_val_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_678_; 
v_val_668_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_678_ == 0)
{
v___x_670_ = v___x_666_;
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_val_668_);
lean_dec(v___x_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_array_get_size(v_items_664_);
lean_dec_ref(v_items_664_);
v___x_673_ = lean_nat_dec_lt(v_val_668_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_del_object(v___x_670_);
lean_dec(v_val_668_);
v___x_674_ = lean_box(0);
return v___x_674_;
}
else
{
lean_object* v___x_676_; 
if (v_isShared_671_ == 0)
{
v___x_676_ = v___x_670_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_val_668_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_cmp_681_, lean_object* v_k_682_, lean_object* v_t_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_681_, v_k_682_, v_t_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0(lean_object* v_00_u03b1_685_, lean_object* v_cmp_686_, lean_object* v_00_u03b4_687_, lean_object* v_t_688_, lean_object* v_k_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_686_, v_t_688_, v_k_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object* v_cmp_691_, lean_object* v_k_692_, lean_object* v_t_693_){
_start:
{
lean_object* v___x_694_; 
lean_inc_ref(v_t_693_);
v___x_694_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_691_, v_k_692_, v_t_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; 
lean_dec_ref(v_t_693_);
v___x_695_ = lean_box(0);
return v___x_695_;
}
else
{
lean_object* v_val_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_705_; 
v_val_696_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_705_ == 0)
{
v___x_698_ = v___x_694_;
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_val_696_);
lean_dec(v___x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_705_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_items_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v_items_700_ = lean_ctor_get(v_t_693_, 0);
lean_inc_ref(v_items_700_);
lean_dec_ref(v_t_693_);
v___x_701_ = lean_array_fget(v_items_700_, v_val_696_);
lean_dec(v_val_696_);
lean_dec_ref(v_items_700_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_701_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f(lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_cmp_708_, lean_object* v_k_709_, lean_object* v_t_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_708_, v_k_709_, v_t_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f___redArg(lean_object* v_cmp_712_, lean_object* v_k_713_, lean_object* v_t_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_712_, v_k_713_, v_t_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_box(0);
return v___x_716_;
}
else
{
lean_object* v_val_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_725_; 
v_val_717_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_725_ == 0)
{
v___x_719_ = v___x_715_;
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_val_717_);
lean_dec(v___x_715_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_snd_721_; lean_object* v___x_723_; 
v_snd_721_ = lean_ctor_get(v_val_717_, 1);
lean_inc(v_snd_721_);
lean_dec(v_val_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v_snd_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_snd_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_cmp_728_, lean_object* v_k_729_, lean_object* v_t_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_728_, v_k_729_, v_t_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
else
{
lean_object* v_val_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_741_; 
v_val_733_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_741_ == 0)
{
v___x_735_ = v___x_731_;
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_val_733_);
lean_dec(v___x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_741_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_snd_737_; lean_object* v___x_739_; 
v_snd_737_ = lean_ctor_get(v_val_733_, 1);
lean_inc(v_snd_737_);
lean_dec(v_val_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_snd_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_snd_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object* v_cmp_742_, lean_object* v_k_743_, lean_object* v_v_744_, lean_object* v_t_745_){
_start:
{
lean_object* v_items_746_; lean_object* v_indices_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_758_; 
v_items_746_ = lean_ctor_get(v_t_745_, 0);
v_indices_747_ = lean_ctor_get(v_t_745_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_t_745_);
if (v_isSharedCheck_758_ == 0)
{
v___x_749_ = v_t_745_;
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_indices_747_);
lean_inc(v_items_746_);
lean_dec(v_t_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
lean_inc(v_k_743_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_k_743_);
lean_ctor_set(v___x_751_, 1, v_v_744_);
lean_inc_ref(v_items_746_);
v___x_752_ = lean_array_push(v_items_746_, v___x_751_);
v___x_753_ = lean_array_get_size(v_items_746_);
lean_dec_ref(v_items_746_);
v___x_754_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_742_, v_k_743_, v___x_753_, v_indices_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_754_);
lean_ctor_set(v___x_749_, 0, v___x_752_);
v___x_756_ = v___x_749_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_cmp_761_, lean_object* v_k_762_, lean_object* v_v_763_, lean_object* v_t_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_761_, v_k_762_, v_v_763_, v_t_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___redArg(lean_object* v_cmp_766_, lean_object* v_k_767_, lean_object* v_f_768_, lean_object* v_t_769_){
_start:
{
lean_object* v___x_770_; 
lean_inc_ref(v_t_769_);
lean_inc(v_k_767_);
lean_inc_ref(v_cmp_766_);
v___x_770_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_766_, v_k_767_, v_t_769_);
if (lean_obj_tag(v___x_770_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_k_767_);
lean_dec_ref(v_cmp_766_);
v_val_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_806_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_806_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_806_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_items_775_; lean_object* v_indices_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_805_; 
v_items_775_ = lean_ctor_get(v_t_769_, 0);
v_indices_776_ = lean_ctor_get(v_t_769_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_t_769_);
if (v_isSharedCheck_805_ == 0)
{
v___x_778_ = v_t_769_;
v_isShared_779_ = v_isSharedCheck_805_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_indices_776_);
lean_inc(v_items_775_);
lean_dec(v_t_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_805_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = lean_array_get_size(v_items_775_);
v___x_781_ = lean_nat_dec_lt(v_val_771_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_783_; 
lean_del_object(v___x_773_);
lean_dec(v_val_771_);
lean_dec(v_f_768_);
if (v_isShared_779_ == 0)
{
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_items_775_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_indices_776_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v_v_785_; lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_804_; 
v_v_785_ = lean_array_fget(v_items_775_, v_val_771_);
v_fst_786_ = lean_ctor_get(v_v_785_, 0);
v_snd_787_ = lean_ctor_get(v_v_785_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_v_785_);
if (v_isSharedCheck_804_ == 0)
{
v___x_789_ = v_v_785_;
v_isShared_790_ = v_isSharedCheck_804_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snd_787_);
lean_inc(v_fst_786_);
lean_dec(v_v_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_804_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v_xs_x27_792_; lean_object* v___x_794_; 
v___x_791_ = lean_box(0);
v_xs_x27_792_ = lean_array_fset(v_items_775_, v_val_771_, v___x_791_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_snd_787_);
v___x_794_ = v___x_773_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_snd_787_);
v___x_794_ = v_reuseFailAlloc_803_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = lean_apply_1(v_f_768_, v___x_794_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_795_);
v___x_797_ = v___x_789_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_786_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_802_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_array_fset(v_xs_x27_792_, v_val_771_, v___x_797_);
lean_dec(v_val_771_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_798_);
v___x_800_ = v___x_778_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_indices_776_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
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
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v___x_770_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_apply_1(v_f_768_, v___x_807_);
v___x_809_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_766_, v_k_767_, v___x_808_, v_t_769_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_cmp_812_, lean_object* v_k_813_, lean_object* v_f_814_, lean_object* v_t_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lake_Toml_RBDict_alter___redArg(v_cmp_812_, v_k_813_, v_f_814_, v_t_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert___redArg(lean_object* v_cmp_817_, lean_object* v_k_818_, lean_object* v_v_819_, lean_object* v_t_820_){
_start:
{
lean_object* v___x_821_; 
lean_inc_ref(v_t_820_);
lean_inc(v_k_818_);
lean_inc_ref(v_cmp_817_);
v___x_821_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_817_, v_k_818_, v_t_820_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v_val_822_; lean_object* v_items_823_; lean_object* v_indices_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v___x_821_, 1);
v_items_823_ = lean_ctor_get(v_t_820_, 0);
v_indices_824_ = lean_ctor_get(v_t_820_, 1);
v___x_825_ = lean_array_get_size(v_items_823_);
v___x_826_ = lean_nat_dec_lt(v_val_822_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec(v_val_822_);
v___x_827_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_817_, v_k_818_, v_v_819_, v_t_820_);
return v___x_827_;
}
else
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_indices_824_);
lean_inc_ref(v_items_823_);
lean_dec_ref(v_cmp_817_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_t_820_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_837_ = lean_ctor_get(v_t_820_, 1);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_t_820_, 0);
lean_dec(v_unused_838_);
v___x_829_ = v_t_820_;
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
else
{
lean_dec(v_t_820_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_k_818_);
lean_ctor_set(v___x_831_, 1, v_v_819_);
v___x_832_ = lean_array_fset(v_items_823_, v_val_822_, v___x_831_);
lean_dec(v_val_822_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_832_);
v___x_834_ = v___x_829_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_indices_824_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v___x_839_; 
lean_dec(v___x_821_);
v___x_839_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_817_, v_k_818_, v_v_819_, v_t_820_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_cmp_842_, lean_object* v_k_843_, lean_object* v_v_844_, lean_object* v_t_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_842_, v_k_843_, v_v_844_, v_t_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(lean_object* v_cmp_847_, lean_object* v_as_848_, size_t v_i_849_, size_t v_stop_850_, lean_object* v_b_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_eq(v_i_849_, v_stop_850_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_856_; size_t v___x_857_; size_t v___x_858_; 
v___x_853_ = lean_array_uget_borrowed(v_as_848_, v_i_849_);
v_fst_854_ = lean_ctor_get(v___x_853_, 0);
v_snd_855_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_snd_855_);
lean_inc(v_fst_854_);
lean_inc_ref(v_cmp_847_);
v___x_856_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_847_, v_fst_854_, v_snd_855_, v_b_851_);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_849_, v___x_857_);
v_i_849_ = v___x_858_;
v_b_851_ = v___x_856_;
goto _start;
}
else
{
lean_dec_ref(v_cmp_847_);
return v_b_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg___boxed(lean_object* v_cmp_860_, lean_object* v_as_861_, lean_object* v_i_862_, lean_object* v_stop_863_, lean_object* v_b_864_){
_start:
{
size_t v_i_boxed_865_; size_t v_stop_boxed_866_; lean_object* v_res_867_; 
v_i_boxed_865_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_stop_boxed_866_ = lean_unbox_usize(v_stop_863_);
lean_dec(v_stop_863_);
v_res_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_860_, v_as_861_, v_i_boxed_865_, v_stop_boxed_866_, v_b_864_);
lean_dec_ref(v_as_861_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg(lean_object* v_cmp_868_, lean_object* v_self_869_, lean_object* v_other_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get_size(v_other_870_);
v___x_873_ = lean_nat_dec_lt(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_dec_ref(v_cmp_868_);
return v_self_869_;
}
else
{
uint8_t v___x_874_; 
v___x_874_ = lean_nat_dec_le(v___x_872_, v___x_872_);
if (v___x_874_ == 0)
{
if (v___x_873_ == 0)
{
lean_dec_ref(v_cmp_868_);
return v_self_869_;
}
else
{
size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((size_t)0ULL);
v___x_876_ = lean_usize_of_nat(v___x_872_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_868_, v_other_870_, v___x_875_, v___x_876_, v_self_869_);
return v___x_877_;
}
}
else
{
size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; 
v___x_878_ = ((size_t)0ULL);
v___x_879_ = lean_usize_of_nat(v___x_872_);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_868_, v_other_870_, v___x_878_, v___x_879_, v_self_869_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg___boxed(lean_object* v_cmp_881_, lean_object* v_self_882_, lean_object* v_other_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_881_, v_self_882_, v_other_883_);
lean_dec_ref(v_other_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray(lean_object* v_00_u03b1_885_, lean_object* v_00_u03b2_886_, lean_object* v_cmp_887_, lean_object* v_self_888_, lean_object* v_other_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_887_, v_self_888_, v_other_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___boxed(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_cmp_893_, lean_object* v_self_894_, lean_object* v_other_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lake_Toml_RBDict_appendArray(v_00_u03b1_891_, v_00_u03b2_892_, v_cmp_893_, v_self_894_, v_other_895_);
lean_dec_ref(v_other_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_cmp_899_, lean_object* v_as_900_, size_t v_i_901_, size_t v_stop_902_, lean_object* v_b_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_899_, v_as_900_, v_i_901_, v_stop_902_, v_b_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___boxed(lean_object* v_00_u03b1_905_, lean_object* v_00_u03b2_906_, lean_object* v_cmp_907_, lean_object* v_as_908_, lean_object* v_i_909_, lean_object* v_stop_910_, lean_object* v_b_911_){
_start:
{
size_t v_i_boxed_912_; size_t v_stop_boxed_913_; lean_object* v_res_914_; 
v_i_boxed_912_ = lean_unbox_usize(v_i_909_);
lean_dec(v_i_909_);
v_stop_boxed_913_ = lean_unbox_usize(v_stop_910_);
lean_dec(v_stop_910_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(v_00_u03b1_905_, v_00_u03b2_906_, v_cmp_907_, v_as_908_, v_i_boxed_912_, v_stop_boxed_913_, v_b_911_);
lean_dec_ref(v_as_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd___redArg(lean_object* v_cmp_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_appendArray___boxed), 5, 3);
lean_closure_set(v___x_916_, 0, lean_box(0));
lean_closure_set(v___x_916_, 1, lean_box(0));
lean_closure_set(v___x_916_, 2, v_cmp_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd(lean_object* v_00_u03b1_917_, lean_object* v_00_u03b2_918_, lean_object* v_cmp_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_appendArray___boxed), 5, 3);
lean_closure_set(v___x_920_, 0, lean_box(0));
lean_closure_set(v___x_920_, 1, lean_box(0));
lean_closure_set(v___x_920_, 2, v_cmp_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg(lean_object* v_cmp_921_, lean_object* v_self_922_, lean_object* v_other_923_){
_start:
{
lean_object* v_items_924_; lean_object* v___x_925_; 
v_items_924_ = lean_ctor_get(v_other_923_, 0);
v___x_925_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_921_, v_self_922_, v_items_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg___boxed(lean_object* v_cmp_926_, lean_object* v_self_927_, lean_object* v_other_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lake_Toml_RBDict_append___redArg(v_cmp_926_, v_self_927_, v_other_928_);
lean_dec_ref(v_other_928_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append(lean_object* v_00_u03b1_930_, lean_object* v_00_u03b2_931_, lean_object* v_cmp_932_, lean_object* v_self_933_, lean_object* v_other_934_){
_start:
{
lean_object* v_items_935_; lean_object* v___x_936_; 
v_items_935_ = lean_ctor_get(v_other_934_, 0);
v___x_936_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_932_, v_self_933_, v_items_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___boxed(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_cmp_939_, lean_object* v_self_940_, lean_object* v_other_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lake_Toml_RBDict_append(v_00_u03b1_937_, v_00_u03b2_938_, v_cmp_939_, v_self_940_, v_other_941_);
lean_dec_ref(v_other_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend___redArg(lean_object* v_cmp_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_append___boxed), 5, 3);
lean_closure_set(v___x_944_, 0, lean_box(0));
lean_closure_set(v___x_944_, 1, lean_box(0));
lean_closure_set(v___x_944_, 2, v_cmp_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend(lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_cmp_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_append___boxed), 5, 3);
lean_closure_set(v___x_948_, 0, lean_box(0));
lean_closure_set(v___x_948_, 1, lean_box(0));
lean_closure_set(v___x_948_, 2, v_cmp_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg___lam__0(lean_object* v_f_949_, lean_object* v_x_950_){
_start:
{
lean_object* v_fst_951_; lean_object* v_snd_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_fst_951_ = lean_ctor_get(v_x_950_, 0);
v_snd_952_ = lean_ctor_get(v_x_950_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_x_950_);
if (v_isSharedCheck_960_ == 0)
{
v___x_954_ = v_x_950_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snd_952_);
lean_inc(v_fst_951_);
lean_dec(v_x_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
lean_inc(v_fst_951_);
v___x_956_ = lean_apply_2(v_f_949_, v_fst_951_, v_snd_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_fst_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg(lean_object* v_f_980_, lean_object* v_t_981_){
_start:
{
lean_object* v_items_982_; lean_object* v_indices_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_995_; 
v_items_982_ = lean_ctor_get(v_t_981_, 0);
v_indices_983_ = lean_ctor_get(v_t_981_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_t_981_);
if (v_isSharedCheck_995_ == 0)
{
v___x_985_ = v_t_981_;
v_isShared_986_ = v_isSharedCheck_995_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_indices_983_);
lean_inc(v_items_982_);
lean_dec(v_t_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_995_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___f_987_; lean_object* v___x_988_; size_t v_sz_989_; size_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___f_987_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_987_, 0, v_f_980_);
v___x_988_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_sz_989_ = lean_array_size(v_items_982_);
v___x_990_ = ((size_t)0ULL);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_988_, v___f_987_, v_sz_989_, v___x_990_, v_items_982_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_991_);
v___x_993_ = v___x_985_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_indices_983_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map(lean_object* v_00_u03b1_996_, lean_object* v_00_u03b2_997_, lean_object* v_00_u03b3_998_, lean_object* v_cmp_999_, lean_object* v_f_1000_, lean_object* v_t_1001_){
_start:
{
lean_object* v_items_1002_; lean_object* v_indices_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1015_; 
v_items_1002_ = lean_ctor_get(v_t_1001_, 0);
v_indices_1003_ = lean_ctor_get(v_t_1001_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_t_1001_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1005_ = v_t_1001_;
v_isShared_1006_ = v_isSharedCheck_1015_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_indices_1003_);
lean_inc(v_items_1002_);
lean_dec(v_t_1001_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1015_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___f_1007_; lean_object* v___x_1008_; size_t v_sz_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___f_1007_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1007_, 0, v_f_1000_);
v___x_1008_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_sz_1009_ = lean_array_size(v_items_1002_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1008_, v___f_1007_, v_sz_1009_, v___x_1010_, v_items_1002_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1011_);
v___x_1013_ = v___x_1005_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_indices_1003_);
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
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_00_u03b3_1018_, lean_object* v_cmp_1019_, lean_object* v_f_1020_, lean_object* v_t_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lake_Toml_RBDict_map(v_00_u03b1_1016_, v_00_u03b2_1017_, v_00_u03b3_1018_, v_cmp_1019_, v_f_1020_, v_t_1021_);
lean_dec_ref(v_cmp_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg___lam__0(lean_object* v_p_1023_, lean_object* v_cmp_1024_, lean_object* v_x1_1025_, lean_object* v_x2_1026_){
_start:
{
lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_fst_1027_ = lean_ctor_get(v_x2_1026_, 0);
lean_inc_n(v_fst_1027_, 2);
v_snd_1028_ = lean_ctor_get(v_x2_1026_, 1);
lean_inc_n(v_snd_1028_, 2);
lean_dec_ref(v_x2_1026_);
v___x_1029_ = lean_apply_2(v_p_1023_, v_fst_1027_, v_snd_1028_);
v___x_1030_ = lean_unbox(v___x_1029_);
if (v___x_1030_ == 0)
{
lean_dec(v_snd_1028_);
lean_dec(v_fst_1027_);
lean_dec_ref(v_cmp_1024_);
return v_x1_1025_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1024_, v_fst_1027_, v_snd_1028_, v_x1_1025_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg(lean_object* v_cmp_1032_, lean_object* v_p_1033_, lean_object* v_t_1034_){
_start:
{
lean_object* v_items_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_items_1035_ = lean_ctor_get(v_t_1034_, 0);
lean_inc_ref(v_items_1035_);
lean_dec_ref(v_t_1034_);
v___x_1036_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = lean_array_get_size(v_items_1035_);
v___x_1039_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1040_ = lean_nat_dec_lt(v___x_1037_, v___x_1038_);
if (v___x_1040_ == 0)
{
lean_dec_ref(v_items_1035_);
lean_dec_ref(v_p_1033_);
lean_dec_ref(v_cmp_1032_);
return v___x_1036_;
}
else
{
lean_object* v___f_1041_; uint8_t v___x_1042_; 
v___f_1041_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filter___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1041_, 0, v_p_1033_);
lean_closure_set(v___f_1041_, 1, v_cmp_1032_);
v___x_1042_ = lean_nat_dec_le(v___x_1038_, v___x_1038_);
if (v___x_1042_ == 0)
{
if (v___x_1040_ == 0)
{
lean_dec_ref(v___f_1041_);
lean_dec_ref(v_items_1035_);
return v___x_1036_;
}
else
{
size_t v___x_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = lean_usize_of_nat(v___x_1038_);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1039_, v___f_1041_, v_items_1035_, v___x_1043_, v___x_1044_, v___x_1036_);
return v___x_1045_;
}
}
else
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = lean_usize_of_nat(v___x_1038_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1039_, v___f_1041_, v_items_1035_, v___x_1046_, v___x_1047_, v___x_1036_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter(lean_object* v_00_u03b1_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_cmp_1051_, lean_object* v_p_1052_, lean_object* v_t_1053_){
_start:
{
lean_object* v_items_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_items_1054_ = lean_ctor_get(v_t_1053_, 0);
lean_inc_ref(v_items_1054_);
lean_dec_ref(v_t_1053_);
v___x_1055_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_array_get_size(v_items_1054_);
v___x_1058_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1059_ = lean_nat_dec_lt(v___x_1056_, v___x_1057_);
if (v___x_1059_ == 0)
{
lean_dec_ref(v_items_1054_);
lean_dec_ref(v_p_1052_);
lean_dec_ref(v_cmp_1051_);
return v___x_1055_;
}
else
{
lean_object* v___f_1060_; uint8_t v___x_1061_; 
v___f_1060_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filter___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1060_, 0, v_p_1052_);
lean_closure_set(v___f_1060_, 1, v_cmp_1051_);
v___x_1061_ = lean_nat_dec_le(v___x_1057_, v___x_1057_);
if (v___x_1061_ == 0)
{
if (v___x_1059_ == 0)
{
lean_dec_ref(v___f_1060_);
lean_dec_ref(v_items_1054_);
return v___x_1055_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1057_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1058_, v___f_1060_, v_items_1054_, v___x_1062_, v___x_1063_, v___x_1055_);
return v___x_1064_;
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1057_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1058_, v___f_1060_, v_items_1054_, v___x_1065_, v___x_1066_, v___x_1055_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg___lam__0(lean_object* v_f_1068_, lean_object* v_cmp_1069_, lean_object* v_x1_1070_, lean_object* v_x2_1071_){
_start:
{
lean_object* v_fst_1072_; lean_object* v_snd_1073_; lean_object* v___x_1074_; 
v_fst_1072_ = lean_ctor_get(v_x2_1071_, 0);
lean_inc_n(v_fst_1072_, 2);
v_snd_1073_ = lean_ctor_get(v_x2_1071_, 1);
lean_inc(v_snd_1073_);
lean_dec_ref(v_x2_1071_);
v___x_1074_ = lean_apply_2(v_f_1068_, v_fst_1072_, v_snd_1073_);
if (lean_obj_tag(v___x_1074_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1076_; 
v_val_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1069_, v_fst_1072_, v_val_1075_, v_x1_1070_);
return v___x_1076_;
}
else
{
lean_dec(v___x_1074_);
lean_dec(v_fst_1072_);
lean_dec_ref(v_cmp_1069_);
return v_x1_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg(lean_object* v_cmp_1077_, lean_object* v_f_1078_, lean_object* v_t_1079_){
_start:
{
lean_object* v_items_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_items_1080_ = lean_ctor_get(v_t_1079_, 0);
lean_inc_ref(v_items_1080_);
lean_dec_ref(v_t_1079_);
v___x_1081_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_array_get_size(v_items_1080_);
v___x_1084_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1085_ = lean_nat_dec_lt(v___x_1082_, v___x_1083_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v_items_1080_);
lean_dec_ref(v_f_1078_);
lean_dec_ref(v_cmp_1077_);
return v___x_1081_;
}
else
{
lean_object* v___f_1086_; uint8_t v___x_1087_; 
v___f_1086_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filterMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1086_, 0, v_f_1078_);
lean_closure_set(v___f_1086_, 1, v_cmp_1077_);
v___x_1087_ = lean_nat_dec_le(v___x_1083_, v___x_1083_);
if (v___x_1087_ == 0)
{
if (v___x_1085_ == 0)
{
lean_dec_ref(v___f_1086_);
lean_dec_ref(v_items_1080_);
return v___x_1081_;
}
else
{
size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_of_nat(v___x_1083_);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1084_, v___f_1086_, v_items_1080_, v___x_1088_, v___x_1089_, v___x_1081_);
return v___x_1090_;
}
}
else
{
size_t v___x_1091_; size_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = lean_usize_of_nat(v___x_1083_);
v___x_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1084_, v___f_1086_, v_items_1080_, v___x_1091_, v___x_1092_, v___x_1081_);
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap(lean_object* v_00_u03b1_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_00_u03b3_1096_, lean_object* v_cmp_1097_, lean_object* v_f_1098_, lean_object* v_t_1099_){
_start:
{
lean_object* v_items_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_items_1100_ = lean_ctor_get(v_t_1099_, 0);
lean_inc_ref(v_items_1100_);
lean_dec_ref(v_t_1099_);
v___x_1101_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_array_get_size(v_items_1100_);
v___x_1104_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1105_ = lean_nat_dec_lt(v___x_1102_, v___x_1103_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v_items_1100_);
lean_dec_ref(v_f_1098_);
lean_dec_ref(v_cmp_1097_);
return v___x_1101_;
}
else
{
lean_object* v___f_1106_; uint8_t v___x_1107_; 
v___f_1106_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filterMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1106_, 0, v_f_1098_);
lean_closure_set(v___f_1106_, 1, v_cmp_1097_);
v___x_1107_ = lean_nat_dec_le(v___x_1103_, v___x_1103_);
if (v___x_1107_ == 0)
{
if (v___x_1105_ == 0)
{
lean_dec_ref(v___f_1106_);
lean_dec_ref(v_items_1100_);
return v___x_1101_;
}
else
{
size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = lean_usize_of_nat(v___x_1103_);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1104_, v___f_1106_, v_items_1100_, v___x_1108_, v___x_1109_, v___x_1101_);
return v___x_1110_;
}
}
else
{
size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = ((size_t)0ULL);
v___x_1112_ = lean_usize_of_nat(v___x_1103_);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1104_, v___f_1106_, v_items_1100_, v___x_1111_, v___x_1112_, v___x_1101_);
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg___lam__0(lean_object* v_f_1114_, lean_object* v_s_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_fst_1117_; lean_object* v_snd_1118_; lean_object* v___x_1119_; 
v_fst_1117_ = lean_ctor_get(v_x_1116_, 0);
lean_inc(v_fst_1117_);
v_snd_1118_ = lean_ctor_get(v_x_1116_, 1);
lean_inc(v_snd_1118_);
lean_dec_ref(v_x_1116_);
v___x_1119_ = lean_apply_3(v_f_1114_, v_s_1115_, v_fst_1117_, v_snd_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg(lean_object* v_inst_1120_, lean_object* v_f_1121_, lean_object* v_init_1122_, lean_object* v_t_1123_){
_start:
{
lean_object* v_toApplicative_1124_; lean_object* v_items_1125_; lean_object* v_toPure_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_toApplicative_1124_ = lean_ctor_get(v_inst_1120_, 0);
v_items_1125_ = lean_ctor_get(v_t_1123_, 0);
lean_inc_ref(v_items_1125_);
lean_dec_ref(v_t_1123_);
v_toPure_1126_ = lean_ctor_get(v_toApplicative_1124_, 1);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_array_get_size(v_items_1125_);
v___x_1129_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_inc(v_toPure_1126_);
lean_dec_ref(v_items_1125_);
lean_dec(v_f_1121_);
lean_dec_ref(v_inst_1120_);
v___x_1130_ = lean_apply_2(v_toPure_1126_, lean_box(0), v_init_1122_);
return v___x_1130_;
}
else
{
lean_object* v___f_1131_; uint8_t v___x_1132_; 
v___f_1131_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1131_, 0, v_f_1121_);
v___x_1132_ = lean_nat_dec_le(v___x_1128_, v___x_1128_);
if (v___x_1132_ == 0)
{
if (v___x_1129_ == 0)
{
lean_object* v___x_1133_; 
lean_inc(v_toPure_1126_);
lean_dec_ref(v___f_1131_);
lean_dec_ref(v_items_1125_);
lean_dec_ref(v_inst_1120_);
v___x_1133_ = lean_apply_2(v_toPure_1126_, lean_box(0), v_init_1122_);
return v___x_1133_;
}
else
{
size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = ((size_t)0ULL);
v___x_1135_ = lean_usize_of_nat(v___x_1128_);
v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1120_, v___f_1131_, v_items_1125_, v___x_1134_, v___x_1135_, v_init_1122_);
return v___x_1136_;
}
}
else
{
size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = lean_usize_of_nat(v___x_1128_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1120_, v___f_1131_, v_items_1125_, v___x_1137_, v___x_1138_, v_init_1122_);
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM(lean_object* v_m_1140_, lean_object* v_00_u03c3_1141_, lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_cmp_1144_, lean_object* v_inst_1145_, lean_object* v_f_1146_, lean_object* v_init_1147_, lean_object* v_t_1148_){
_start:
{
lean_object* v_toApplicative_1149_; lean_object* v_items_1150_; lean_object* v_toPure_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_toApplicative_1149_ = lean_ctor_get(v_inst_1145_, 0);
v_items_1150_ = lean_ctor_get(v_t_1148_, 0);
lean_inc_ref(v_items_1150_);
lean_dec_ref(v_t_1148_);
v_toPure_1151_ = lean_ctor_get(v_toApplicative_1149_, 1);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_array_get_size(v_items_1150_);
v___x_1154_ = lean_nat_dec_lt(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
lean_inc(v_toPure_1151_);
lean_dec_ref(v_items_1150_);
lean_dec(v_f_1146_);
lean_dec_ref(v_inst_1145_);
v___x_1155_ = lean_apply_2(v_toPure_1151_, lean_box(0), v_init_1147_);
return v___x_1155_;
}
else
{
lean_object* v___f_1156_; uint8_t v___x_1157_; 
v___f_1156_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1156_, 0, v_f_1146_);
v___x_1157_ = lean_nat_dec_le(v___x_1153_, v___x_1153_);
if (v___x_1157_ == 0)
{
if (v___x_1154_ == 0)
{
lean_object* v___x_1158_; 
lean_inc(v_toPure_1151_);
lean_dec_ref(v___f_1156_);
lean_dec_ref(v_items_1150_);
lean_dec_ref(v_inst_1145_);
v___x_1158_ = lean_apply_2(v_toPure_1151_, lean_box(0), v_init_1147_);
return v___x_1158_;
}
else
{
size_t v___x_1159_; size_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = lean_usize_of_nat(v___x_1153_);
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1145_, v___f_1156_, v_items_1150_, v___x_1159_, v___x_1160_, v_init_1147_);
return v___x_1161_;
}
}
else
{
size_t v___x_1162_; size_t v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = ((size_t)0ULL);
v___x_1163_ = lean_usize_of_nat(v___x_1153_);
v___x_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1145_, v___f_1156_, v_items_1150_, v___x_1162_, v___x_1163_, v_init_1147_);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___boxed(lean_object* v_m_1165_, lean_object* v_00_u03c3_1166_, lean_object* v_00_u03b1_1167_, lean_object* v_00_u03b2_1168_, lean_object* v_cmp_1169_, lean_object* v_inst_1170_, lean_object* v_f_1171_, lean_object* v_init_1172_, lean_object* v_t_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lake_Toml_RBDict_foldM(v_m_1165_, v_00_u03c3_1166_, v_00_u03b1_1167_, v_00_u03b2_1168_, v_cmp_1169_, v_inst_1170_, v_f_1171_, v_init_1172_, v_t_1173_);
lean_dec_ref(v_cmp_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___redArg(lean_object* v_f_1175_, lean_object* v_init_1176_, lean_object* v_t_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v_items_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1178_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_items_1179_ = lean_ctor_get(v_t_1177_, 0);
lean_inc_ref(v_items_1179_);
lean_dec_ref(v_t_1177_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = lean_array_get_size(v_items_1179_);
v___x_1182_ = lean_nat_dec_lt(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_dec_ref(v_items_1179_);
lean_dec(v_f_1175_);
return v_init_1176_;
}
else
{
lean_object* v___f_1183_; size_t v___x_1184_; size_t v___x_1185_; lean_object* v___x_1186_; 
v___f_1183_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1183_, 0, v_f_1175_);
v___x_1184_ = ((size_t)0ULL);
v___x_1185_ = lean_usize_of_nat(v___x_1181_);
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1178_, v___f_1183_, v_items_1179_, v___x_1184_, v___x_1185_, v_init_1176_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold(lean_object* v_00_u03c3_1187_, lean_object* v_00_u03b1_1188_, lean_object* v_00_u03b2_1189_, lean_object* v_cmp_1190_, lean_object* v_f_1191_, lean_object* v_init_1192_, lean_object* v_t_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v_items_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1194_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_items_1195_ = lean_ctor_get(v_t_1193_, 0);
lean_inc_ref(v_items_1195_);
lean_dec_ref(v_t_1193_);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_items_1195_);
v___x_1198_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_items_1195_);
lean_dec(v_f_1191_);
return v_init_1192_;
}
else
{
lean_object* v___f_1199_; size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v___f_1199_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1199_, 0, v_f_1191_);
v___x_1200_ = ((size_t)0ULL);
v___x_1201_ = lean_usize_of_nat(v___x_1197_);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1194_, v___f_1199_, v_items_1195_, v___x_1200_, v___x_1201_, v_init_1192_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___boxed(lean_object* v_00_u03c3_1203_, lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_cmp_1206_, lean_object* v_f_1207_, lean_object* v_init_1208_, lean_object* v_t_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lake_Toml_RBDict_fold(v_00_u03c3_1203_, v_00_u03b1_1204_, v_00_u03b2_1205_, v_cmp_1206_, v_f_1207_, v_init_1208_, v_t_1209_);
lean_dec_ref(v_cmp_1206_);
return v_res_1210_;
}
}
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Data_Dict(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
