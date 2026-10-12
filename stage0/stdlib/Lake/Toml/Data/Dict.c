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
lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Lake_Toml_instInhabitedRBDict_default___redArg___closed__1));
return v___x_7_;
}
}
LEAN_EXPORT void l_Lake_Toml_instInhabitedRBDict_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_8_;
v_res_8_ = l_Lake_Toml_instInhabitedRBDict_default___redArg();
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___redArg___boxed(lean_object* v___dummy_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_Toml_instInhabitedRBDict_default___redArg();
return v_res_10_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lake_Toml_instInhabitedRBDict_default___redArg();
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_cmp_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lake_Toml_instInhabitedRBDict_default___closed__0, &l_Lake_Toml_instInhabitedRBDict_default___closed__0_once, _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict_default___boxed(lean_object* v_00_u03b1_16_, lean_object* v_00_u03b2_17_, lean_object* v_cmp_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_Toml_instInhabitedRBDict_default(v_00_u03b1_16_, v_00_u03b2_17_, v_cmp_18_);
lean_dec_ref(v_cmp_18_);
return v_res_19_;
}
}
lean_object* l_Lake_Toml_instInhabitedRBDict___redArg(){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lake_Toml_instInhabitedRBDict_default___closed__0, &l_Lake_Toml_instInhabitedRBDict_default___closed__0_once, _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT void l_Lake_Toml_instInhabitedRBDict___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_22_;
v_res_22_ = l_Lake_Toml_instInhabitedRBDict___redArg();
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___redArg___boxed(lean_object* v___dummy_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_Toml_instInhabitedRBDict___redArg();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict(lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lake_Toml_instInhabitedRBDict_default___closed__0, &l_Lake_Toml_instInhabitedRBDict_default___closed__0_once, _init_l_Lake_Toml_instInhabitedRBDict_default___closed__0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedRBDict___boxed(lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lake_Toml_instInhabitedRBDict(v_a_29_, v_a_30_, v_a_31_);
lean_dec_ref(v_a_31_);
return v_res_32_;
}
}
lean_object* l_Lake_Toml_RBDict_empty___redArg(){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = ((lean_object*)(l_Lake_Toml_RBDict_empty___redArg___closed__1));
return v___x_39_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_40_;
v_res_40_ = l_Lake_Toml_RBDict_empty___redArg();
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___redArg___boxed(lean_object* v___dummy_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lake_Toml_RBDict_empty___redArg();
return v_res_42_;
}
}
static lean_object* _init_l_Lake_Toml_RBDict_empty___closed__0(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_cmp_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_empty___boxed(lean_object* v_00_u03b1_48_, lean_object* v_00_u03b2_49_, lean_object* v_cmp_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lake_Toml_RBDict_empty(v_00_u03b1_48_, v_00_u03b2_49_, v_cmp_50_);
lean_dec_ref(v_cmp_50_);
return v_res_51_;
}
}
lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
return v___x_53_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_54_;
v_res_54_ = l_Lake_Toml_RBDict_instEmptyCollection___redArg();
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___redArg___boxed(lean_object* v___dummy_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_Toml_RBDict_instEmptyCollection___redArg();
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_cmp_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instEmptyCollection___boxed(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_cmp_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lake_Toml_RBDict_instEmptyCollection(v_00_u03b1_61_, v_00_u03b2_62_, v_cmp_63_);
lean_dec_ref(v_cmp_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg(lean_object* v_capacity_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_mk_empty_array_with_capacity(v_capacity_65_);
v___x_67_ = lean_box(1);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___redArg___boxed(lean_object* v_capacity_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_69_);
lean_dec(v_capacity_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_cmp_73_, lean_object* v_capacity_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lake_Toml_RBDict_mkEmpty___redArg(v_capacity_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_mkEmpty___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_cmp_78_, lean_object* v_capacity_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_Toml_RBDict_mkEmpty(v_00_u03b1_76_, v_00_u03b2_77_, v_cmp_78_, v_capacity_79_);
lean_dec(v_capacity_79_);
lean_dec_ref(v_cmp_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(lean_object* v_cmp_81_, lean_object* v_k_82_, lean_object* v_v_83_, lean_object* v_t_84_){
_start:
{
if (lean_obj_tag(v_t_84_) == 0)
{
lean_object* v_size_85_; lean_object* v_k_86_; lean_object* v_v_87_; lean_object* v_l_88_; lean_object* v_r_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_370_; 
v_size_85_ = lean_ctor_get(v_t_84_, 0);
v_k_86_ = lean_ctor_get(v_t_84_, 1);
v_v_87_ = lean_ctor_get(v_t_84_, 2);
v_l_88_ = lean_ctor_get(v_t_84_, 3);
v_r_89_ = lean_ctor_get(v_t_84_, 4);
v_isSharedCheck_370_ = !lean_is_exclusive(v_t_84_);
if (v_isSharedCheck_370_ == 0)
{
v___x_91_ = v_t_84_;
v_isShared_92_ = v_isSharedCheck_370_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_r_89_);
lean_inc(v_l_88_);
lean_inc(v_v_87_);
lean_inc(v_k_86_);
lean_inc(v_size_85_);
lean_dec(v_t_84_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_370_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; uint8_t v___x_94_; 
lean_inc_ref(v_cmp_81_);
lean_inc(v_k_86_);
lean_inc(v_k_82_);
v___x_93_ = lean_apply_2(v_cmp_81_, v_k_82_, v_k_86_);
v___x_94_ = lean_unbox(v___x_93_);
switch(v___x_94_)
{
case 0:
{
lean_object* v_impl_95_; lean_object* v___x_96_; 
lean_dec(v_size_85_);
v_impl_95_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_81_, v_k_82_, v_v_83_, v_l_88_);
v___x_96_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_89_) == 0)
{
lean_object* v_size_97_; lean_object* v_size_98_; lean_object* v_k_99_; lean_object* v_v_100_; lean_object* v_l_101_; lean_object* v_r_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_size_97_ = lean_ctor_get(v_r_89_, 0);
v_size_98_ = lean_ctor_get(v_impl_95_, 0);
v_k_99_ = lean_ctor_get(v_impl_95_, 1);
v_v_100_ = lean_ctor_get(v_impl_95_, 2);
v_l_101_ = lean_ctor_get(v_impl_95_, 3);
v_r_102_ = lean_ctor_get(v_impl_95_, 4);
lean_inc(v_r_102_);
v___x_103_ = lean_unsigned_to_nat(3u);
v___x_104_ = lean_nat_mul(v___x_103_, v_size_97_);
v___x_105_ = lean_nat_dec_lt(v___x_104_, v_size_98_);
lean_dec(v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec(v_r_102_);
v___x_106_ = lean_nat_add(v___x_96_, v_size_98_);
v___x_107_ = lean_nat_add(v___x_106_, v_size_97_);
lean_dec(v___x_106_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 3, v_impl_95_);
lean_ctor_set(v___x_91_, 0, v___x_107_);
v___x_109_ = v___x_91_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_110_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_110_, 4, v_r_89_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_176_; 
lean_inc(v_l_101_);
lean_inc(v_v_100_);
lean_inc(v_k_99_);
lean_inc(v_size_98_);
v_isSharedCheck_176_ = !lean_is_exclusive(v_impl_95_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; 
v_unused_177_ = lean_ctor_get(v_impl_95_, 4);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_impl_95_, 3);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_impl_95_, 2);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_impl_95_, 1);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_impl_95_, 0);
lean_dec(v_unused_181_);
v___x_112_ = v_impl_95_;
v_isShared_113_ = v_isSharedCheck_176_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_impl_95_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_176_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_size_114_; lean_object* v_size_115_; lean_object* v_k_116_; lean_object* v_v_117_; lean_object* v_l_118_; lean_object* v_r_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_size_114_ = lean_ctor_get(v_l_101_, 0);
v_size_115_ = lean_ctor_get(v_r_102_, 0);
v_k_116_ = lean_ctor_get(v_r_102_, 1);
v_v_117_ = lean_ctor_get(v_r_102_, 2);
v_l_118_ = lean_ctor_get(v_r_102_, 3);
v_r_119_ = lean_ctor_get(v_r_102_, 4);
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_mul(v___x_120_, v_size_114_);
v___x_122_ = lean_nat_dec_lt(v_size_115_, v___x_121_);
lean_dec(v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_151_; 
lean_inc(v_r_119_);
lean_inc(v_l_118_);
lean_inc(v_v_117_);
lean_inc(v_k_116_);
v_isSharedCheck_151_ = !lean_is_exclusive(v_r_102_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; lean_object* v_unused_155_; lean_object* v_unused_156_; 
v_unused_152_ = lean_ctor_get(v_r_102_, 4);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_r_102_, 3);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_r_102_, 2);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_r_102_, 1);
lean_dec(v_unused_155_);
v_unused_156_ = lean_ctor_get(v_r_102_, 0);
lean_dec(v_unused_156_);
v___x_124_ = v_r_102_;
v_isShared_125_ = v_isSharedCheck_151_;
goto v_resetjp_123_;
}
else
{
lean_dec(v_r_102_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_151_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___x_139_; lean_object* v___y_141_; 
v___x_126_ = lean_nat_add(v___x_96_, v_size_98_);
lean_dec(v_size_98_);
v___x_127_ = lean_nat_add(v___x_126_, v_size_97_);
lean_dec(v___x_126_);
v___x_139_ = lean_nat_add(v___x_96_, v_size_114_);
if (lean_obj_tag(v_l_118_) == 0)
{
lean_object* v_size_149_; 
v_size_149_ = lean_ctor_get(v_l_118_, 0);
lean_inc(v_size_149_);
v___y_141_ = v_size_149_;
goto v___jp_140_;
}
else
{
lean_object* v___x_150_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___y_141_ = v___x_150_;
goto v___jp_140_;
}
v___jp_128_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_nat_add(v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec(v___y_130_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 4, v_r_89_);
lean_ctor_set(v___x_124_, 3, v_r_119_);
lean_ctor_set(v___x_124_, 2, v_v_87_);
lean_ctor_set(v___x_124_, 1, v_k_86_);
lean_ctor_set(v___x_124_, 0, v___x_132_);
v___x_134_ = v___x_124_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_r_119_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_r_89_);
v___x_134_ = v_reuseFailAlloc_138_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_134_);
lean_ctor_set(v___x_112_, 3, v___y_129_);
lean_ctor_set(v___x_112_, 2, v_v_117_);
lean_ctor_set(v___x_112_, 1, v_k_116_);
lean_ctor_set(v___x_112_, 0, v___x_127_);
v___x_136_ = v___x_112_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_k_116_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_v_117_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v___y_129_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_nat_add(v___x_139_, v___y_141_);
lean_dec(v___y_141_);
lean_dec(v___x_139_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v_l_118_);
lean_ctor_set(v___x_91_, 3, v_l_101_);
lean_ctor_set(v___x_91_, 2, v_v_100_);
lean_ctor_set(v___x_91_, 1, v_k_99_);
lean_ctor_set(v___x_91_, 0, v___x_142_);
v___x_144_ = v___x_91_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_99_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_100_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_l_101_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_l_118_);
v___x_144_ = v_reuseFailAlloc_148_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; 
v___x_145_ = lean_nat_add(v___x_96_, v_size_97_);
if (lean_obj_tag(v_r_119_) == 0)
{
lean_object* v_size_146_; 
v_size_146_ = lean_ctor_get(v_r_119_, 0);
lean_inc(v_size_146_);
v___y_129_ = v___x_144_;
v___y_130_ = v___x_145_;
v___y_131_ = v_size_146_;
goto v___jp_128_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___y_129_ = v___x_144_;
v___y_130_ = v___x_145_;
v___y_131_ = v___x_147_;
goto v___jp_128_;
}
}
}
}
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
lean_del_object(v___x_91_);
v___x_157_ = lean_nat_add(v___x_96_, v_size_98_);
lean_dec(v_size_98_);
v___x_158_ = lean_nat_add(v___x_157_, v_size_97_);
lean_dec(v___x_157_);
v___x_159_ = lean_nat_add(v___x_96_, v_size_97_);
v___x_160_ = lean_nat_add(v___x_159_, v_size_115_);
lean_dec(v___x_159_);
lean_inc_ref(v_r_89_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_r_89_);
lean_ctor_set(v___x_112_, 3, v_r_102_);
lean_ctor_set(v___x_112_, 2, v_v_87_);
lean_ctor_set(v___x_112_, 1, v_k_86_);
lean_ctor_set(v___x_112_, 0, v___x_160_);
v___x_162_ = v___x_112_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_r_102_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_89_);
v___x_162_ = v_reuseFailAlloc_175_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_isSharedCheck_169_ = !lean_is_exclusive(v_r_89_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; lean_object* v_unused_171_; lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; 
v_unused_170_ = lean_ctor_get(v_r_89_, 4);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_r_89_, 3);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_r_89_, 2);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_r_89_, 1);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_r_89_, 0);
lean_dec(v_unused_174_);
v___x_164_ = v_r_89_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_dec(v_r_89_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 4, v___x_162_);
lean_ctor_set(v___x_164_, 3, v_l_101_);
lean_ctor_set(v___x_164_, 2, v_v_100_);
lean_ctor_set(v___x_164_, 1, v_k_99_);
lean_ctor_set(v___x_164_, 0, v___x_158_);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_99_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_v_100_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v_l_101_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v___x_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_182_; 
v_l_182_ = lean_ctor_get(v_impl_95_, 3);
if (lean_obj_tag(v_l_182_) == 0)
{
lean_object* v_r_183_; lean_object* v_k_184_; lean_object* v_v_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_196_; 
lean_inc_ref(v_l_182_);
v_r_183_ = lean_ctor_get(v_impl_95_, 4);
v_k_184_ = lean_ctor_get(v_impl_95_, 1);
v_v_185_ = lean_ctor_get(v_impl_95_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v_impl_95_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; lean_object* v_unused_198_; 
v_unused_197_ = lean_ctor_get(v_impl_95_, 3);
lean_dec(v_unused_197_);
v_unused_198_ = lean_ctor_get(v_impl_95_, 0);
lean_dec(v_unused_198_);
v___x_187_ = v_impl_95_;
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_r_183_);
lean_inc(v_v_185_);
lean_inc(v_k_184_);
lean_dec(v_impl_95_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_183_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 3, v_r_183_);
lean_ctor_set(v___x_187_, 2, v_v_87_);
lean_ctor_set(v___x_187_, 1, v_k_86_);
lean_ctor_set(v___x_187_, 0, v___x_96_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_r_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v_r_183_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v___x_191_);
lean_ctor_set(v___x_91_, 3, v_l_182_);
lean_ctor_set(v___x_91_, 2, v_v_185_);
lean_ctor_set(v___x_91_, 1, v_k_184_);
lean_ctor_set(v___x_91_, 0, v___x_189_);
v___x_193_ = v___x_91_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_k_184_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_v_185_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_r_199_; 
v_r_199_ = lean_ctor_get(v_impl_95_, 4);
lean_inc(v_r_199_);
if (lean_obj_tag(v_r_199_) == 0)
{
lean_object* v_k_200_; lean_object* v_v_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_224_; 
lean_inc(v_l_182_);
v_k_200_ = lean_ctor_get(v_impl_95_, 1);
v_v_201_ = lean_ctor_get(v_impl_95_, 2);
v_isSharedCheck_224_ = !lean_is_exclusive(v_impl_95_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; lean_object* v_unused_226_; lean_object* v_unused_227_; 
v_unused_225_ = lean_ctor_get(v_impl_95_, 4);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_impl_95_, 3);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_impl_95_, 0);
lean_dec(v_unused_227_);
v___x_203_ = v_impl_95_;
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_v_201_);
lean_inc(v_k_200_);
lean_dec(v_impl_95_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_k_205_; lean_object* v_v_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_220_; 
v_k_205_ = lean_ctor_get(v_r_199_, 1);
v_v_206_ = lean_ctor_get(v_r_199_, 2);
v_isSharedCheck_220_ = !lean_is_exclusive(v_r_199_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; lean_object* v_unused_222_; lean_object* v_unused_223_; 
v_unused_221_ = lean_ctor_get(v_r_199_, 4);
lean_dec(v_unused_221_);
v_unused_222_ = lean_ctor_get(v_r_199_, 3);
lean_dec(v_unused_222_);
v_unused_223_ = lean_ctor_get(v_r_199_, 0);
lean_dec(v_unused_223_);
v___x_208_ = v_r_199_;
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_v_206_);
lean_inc(v_k_205_);
lean_dec(v_r_199_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_unsigned_to_nat(3u);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 4, v_l_182_);
lean_ctor_set(v___x_208_, 3, v_l_182_);
lean_ctor_set(v___x_208_, 2, v_v_201_);
lean_ctor_set(v___x_208_, 1, v_k_200_);
lean_ctor_set(v___x_208_, 0, v___x_96_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_200_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_v_201_);
lean_ctor_set(v_reuseFailAlloc_219_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_219_, 4, v_l_182_);
v___x_212_ = v_reuseFailAlloc_219_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 4, v_l_182_);
lean_ctor_set(v___x_203_, 2, v_v_87_);
lean_ctor_set(v___x_203_, 1, v_k_86_);
lean_ctor_set(v___x_203_, 0, v___x_96_);
v___x_214_ = v___x_203_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_l_182_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v_l_182_);
v___x_214_ = v_reuseFailAlloc_218_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_216_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v___x_214_);
lean_ctor_set(v___x_91_, 3, v___x_212_);
lean_ctor_set(v___x_91_, 2, v_v_206_);
lean_ctor_set(v___x_91_, 1, v_k_205_);
lean_ctor_set(v___x_91_, 0, v___x_210_);
v___x_216_ = v___x_91_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_k_205_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_v_206_);
lean_ctor_set(v_reuseFailAlloc_217_, 3, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_217_, 4, v___x_214_);
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
}
else
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_unsigned_to_nat(2u);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v_r_199_);
lean_ctor_set(v___x_91_, 3, v_impl_95_);
lean_ctor_set(v___x_91_, 0, v___x_228_);
v___x_230_ = v___x_91_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_r_199_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
case 1:
{
lean_object* v___x_233_; 
lean_dec(v_v_87_);
lean_dec(v_k_86_);
lean_dec_ref(v_cmp_81_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 2, v_v_83_);
lean_ctor_set(v___x_91_, 1, v_k_82_);
v___x_233_ = v___x_91_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_size_85_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_k_82_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_v_83_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_l_88_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_r_89_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
default: 
{
lean_object* v_impl_235_; lean_object* v___x_236_; 
lean_dec(v_size_85_);
v_impl_235_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_81_, v_k_82_, v_v_83_, v_r_89_);
v___x_236_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_88_) == 0)
{
lean_object* v_size_237_; lean_object* v_size_238_; lean_object* v_k_239_; lean_object* v_v_240_; lean_object* v_l_241_; lean_object* v_r_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_size_237_ = lean_ctor_get(v_l_88_, 0);
v_size_238_ = lean_ctor_get(v_impl_235_, 0);
v_k_239_ = lean_ctor_get(v_impl_235_, 1);
v_v_240_ = lean_ctor_get(v_impl_235_, 2);
v_l_241_ = lean_ctor_get(v_impl_235_, 3);
lean_inc(v_l_241_);
v_r_242_ = lean_ctor_get(v_impl_235_, 4);
v___x_243_ = lean_unsigned_to_nat(3u);
v___x_244_ = lean_nat_mul(v___x_243_, v_size_237_);
v___x_245_ = lean_nat_dec_lt(v___x_244_, v_size_238_);
lean_dec(v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_l_241_);
v___x_246_ = lean_nat_add(v___x_236_, v_size_237_);
v___x_247_ = lean_nat_add(v___x_246_, v_size_238_);
lean_dec(v___x_246_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v_impl_235_);
lean_ctor_set(v___x_91_, 0, v___x_247_);
v___x_249_ = v___x_91_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_l_88_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v_impl_235_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
else
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_r_242_);
lean_inc(v_v_240_);
lean_inc(v_k_239_);
lean_inc(v_size_238_);
v_isSharedCheck_314_ = !lean_is_exclusive(v_impl_235_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; 
v_unused_315_ = lean_ctor_get(v_impl_235_, 4);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_impl_235_, 3);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_impl_235_, 2);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_impl_235_, 1);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_impl_235_, 0);
lean_dec(v_unused_319_);
v___x_252_ = v_impl_235_;
v_isShared_253_ = v_isSharedCheck_314_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_impl_235_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_314_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_size_254_; lean_object* v_k_255_; lean_object* v_v_256_; lean_object* v_l_257_; lean_object* v_r_258_; lean_object* v_size_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_size_254_ = lean_ctor_get(v_l_241_, 0);
v_k_255_ = lean_ctor_get(v_l_241_, 1);
v_v_256_ = lean_ctor_get(v_l_241_, 2);
v_l_257_ = lean_ctor_get(v_l_241_, 3);
v_r_258_ = lean_ctor_get(v_l_241_, 4);
v_size_259_ = lean_ctor_get(v_r_242_, 0);
v___x_260_ = lean_unsigned_to_nat(2u);
v___x_261_ = lean_nat_mul(v___x_260_, v_size_259_);
v___x_262_ = lean_nat_dec_lt(v_size_254_, v___x_261_);
lean_dec(v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_290_; 
lean_inc(v_r_258_);
lean_inc(v_l_257_);
lean_inc(v_v_256_);
lean_inc(v_k_255_);
v_isSharedCheck_290_ = !lean_is_exclusive(v_l_241_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; lean_object* v_unused_294_; lean_object* v_unused_295_; 
v_unused_291_ = lean_ctor_get(v_l_241_, 4);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_l_241_, 3);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_l_241_, 2);
lean_dec(v_unused_293_);
v_unused_294_ = lean_ctor_get(v_l_241_, 1);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_l_241_, 0);
lean_dec(v_unused_295_);
v___x_264_ = v_l_241_;
v_isShared_265_ = v_isSharedCheck_290_;
goto v_resetjp_263_;
}
else
{
lean_dec(v_l_241_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_290_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v___y_280_; 
v___x_266_ = lean_nat_add(v___x_236_, v_size_237_);
v___x_267_ = lean_nat_add(v___x_266_, v_size_238_);
lean_dec(v_size_238_);
if (lean_obj_tag(v_l_257_) == 0)
{
lean_object* v_size_288_; 
v_size_288_ = lean_ctor_get(v_l_257_, 0);
lean_inc(v_size_288_);
v___y_280_ = v_size_288_;
goto v___jp_279_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___y_280_ = v___x_289_;
goto v___jp_279_;
}
v___jp_268_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_nat_add(v___y_269_, v___y_271_);
lean_dec(v___y_271_);
lean_dec(v___y_269_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 4, v_r_242_);
lean_ctor_set(v___x_264_, 3, v_r_258_);
lean_ctor_set(v___x_264_, 2, v_v_240_);
lean_ctor_set(v___x_264_, 1, v_k_239_);
lean_ctor_set(v___x_264_, 0, v___x_272_);
v___x_274_ = v___x_264_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_k_239_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_v_240_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_r_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_r_242_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v___x_274_);
lean_ctor_set(v___x_252_, 3, v___y_270_);
lean_ctor_set(v___x_252_, 2, v_v_256_);
lean_ctor_set(v___x_252_, 1, v_k_255_);
lean_ctor_set(v___x_252_, 0, v___x_267_);
v___x_276_ = v___x_252_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_k_255_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_v_256_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v___y_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_nat_add(v___x_266_, v___y_280_);
lean_dec(v___y_280_);
lean_dec(v___x_266_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v_l_257_);
lean_ctor_set(v___x_91_, 0, v___x_281_);
v___x_283_ = v___x_91_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_l_88_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_l_257_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_nat_add(v___x_236_, v_size_259_);
if (lean_obj_tag(v_r_258_) == 0)
{
lean_object* v_size_285_; 
v_size_285_ = lean_ctor_get(v_r_258_, 0);
lean_inc(v_size_285_);
v___y_269_ = v___x_284_;
v___y_270_ = v___x_283_;
v___y_271_ = v_size_285_;
goto v___jp_268_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___y_269_ = v___x_284_;
v___y_270_ = v___x_283_;
v___y_271_ = v___x_286_;
goto v___jp_268_;
}
}
}
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
lean_del_object(v___x_91_);
v___x_296_ = lean_nat_add(v___x_236_, v_size_237_);
v___x_297_ = lean_nat_add(v___x_296_, v_size_238_);
lean_dec(v_size_238_);
v___x_298_ = lean_nat_add(v___x_296_, v_size_254_);
lean_dec(v___x_296_);
lean_inc_ref(v_l_88_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v_l_241_);
lean_ctor_set(v___x_252_, 3, v_l_88_);
lean_ctor_set(v___x_252_, 2, v_v_87_);
lean_ctor_set(v___x_252_, 1, v_k_86_);
lean_ctor_set(v___x_252_, 0, v___x_298_);
v___x_300_ = v___x_252_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_l_88_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_l_241_);
v___x_300_ = v_reuseFailAlloc_313_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_isSharedCheck_307_ = !lean_is_exclusive(v_l_88_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; lean_object* v_unused_309_; lean_object* v_unused_310_; lean_object* v_unused_311_; lean_object* v_unused_312_; 
v_unused_308_ = lean_ctor_get(v_l_88_, 4);
lean_dec(v_unused_308_);
v_unused_309_ = lean_ctor_get(v_l_88_, 3);
lean_dec(v_unused_309_);
v_unused_310_ = lean_ctor_get(v_l_88_, 2);
lean_dec(v_unused_310_);
v_unused_311_ = lean_ctor_get(v_l_88_, 1);
lean_dec(v_unused_311_);
v_unused_312_ = lean_ctor_get(v_l_88_, 0);
lean_dec(v_unused_312_);
v___x_302_ = v_l_88_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_l_88_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_r_242_);
lean_ctor_set(v___x_302_, 3, v___x_300_);
lean_ctor_set(v___x_302_, 2, v_v_240_);
lean_ctor_set(v___x_302_, 1, v_k_239_);
lean_ctor_set(v___x_302_, 0, v___x_297_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_k_239_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_v_240_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_r_242_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_320_; 
v_l_320_ = lean_ctor_get(v_impl_235_, 3);
lean_inc(v_l_320_);
if (lean_obj_tag(v_l_320_) == 0)
{
lean_object* v_r_321_; lean_object* v_k_322_; lean_object* v_v_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_346_; 
v_r_321_ = lean_ctor_get(v_impl_235_, 4);
v_k_322_ = lean_ctor_get(v_impl_235_, 1);
v_v_323_ = lean_ctor_get(v_impl_235_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v_impl_235_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; 
v_unused_347_ = lean_ctor_get(v_impl_235_, 3);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_impl_235_, 0);
lean_dec(v_unused_348_);
v___x_325_ = v_impl_235_;
v_isShared_326_ = v_isSharedCheck_346_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_r_321_);
lean_inc(v_v_323_);
lean_inc(v_k_322_);
lean_dec(v_impl_235_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_346_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_k_327_; lean_object* v_v_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_342_; 
v_k_327_ = lean_ctor_get(v_l_320_, 1);
v_v_328_ = lean_ctor_get(v_l_320_, 2);
v_isSharedCheck_342_ = !lean_is_exclusive(v_l_320_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; lean_object* v_unused_344_; lean_object* v_unused_345_; 
v_unused_343_ = lean_ctor_get(v_l_320_, 4);
lean_dec(v_unused_343_);
v_unused_344_ = lean_ctor_get(v_l_320_, 3);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_l_320_, 0);
lean_dec(v_unused_345_);
v___x_330_ = v_l_320_;
v_isShared_331_ = v_isSharedCheck_342_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_v_328_);
lean_inc(v_k_327_);
lean_dec(v_l_320_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_342_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_321_, 2);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 4, v_r_321_);
lean_ctor_set(v___x_330_, 3, v_r_321_);
lean_ctor_set(v___x_330_, 2, v_v_87_);
lean_ctor_set(v___x_330_, 1, v_k_86_);
lean_ctor_set(v___x_330_, 0, v___x_236_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_r_321_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v_r_321_);
v___x_334_ = v_reuseFailAlloc_341_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
lean_inc(v_r_321_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 3, v_r_321_);
lean_ctor_set(v___x_325_, 0, v___x_236_);
v___x_336_ = v___x_325_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_k_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_v_323_);
lean_ctor_set(v_reuseFailAlloc_340_, 3, v_r_321_);
lean_ctor_set(v_reuseFailAlloc_340_, 4, v_r_321_);
v___x_336_ = v_reuseFailAlloc_340_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v___x_336_);
lean_ctor_set(v___x_91_, 3, v___x_334_);
lean_ctor_set(v___x_91_, 2, v_v_328_);
lean_ctor_set(v___x_91_, 1, v_k_327_);
lean_ctor_set(v___x_91_, 0, v___x_332_);
v___x_338_ = v___x_91_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_k_327_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_v_328_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_339_, 4, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
else
{
lean_object* v_r_349_; 
v_r_349_ = lean_ctor_get(v_impl_235_, 4);
lean_inc(v_r_349_);
if (lean_obj_tag(v_r_349_) == 0)
{
lean_object* v_k_350_; lean_object* v_v_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_362_; 
v_k_350_ = lean_ctor_get(v_impl_235_, 1);
v_v_351_ = lean_ctor_get(v_impl_235_, 2);
v_isSharedCheck_362_ = !lean_is_exclusive(v_impl_235_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; lean_object* v_unused_364_; lean_object* v_unused_365_; 
v_unused_363_ = lean_ctor_get(v_impl_235_, 4);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_impl_235_, 3);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_impl_235_, 0);
lean_dec(v_unused_365_);
v___x_353_ = v_impl_235_;
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_v_351_);
lean_inc(v_k_350_);
lean_dec(v_impl_235_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_unsigned_to_nat(3u);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 4, v_l_320_);
lean_ctor_set(v___x_353_, 2, v_v_87_);
lean_ctor_set(v___x_353_, 1, v_k_86_);
lean_ctor_set(v___x_353_, 0, v___x_236_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_l_320_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_l_320_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v_r_349_);
lean_ctor_set(v___x_91_, 3, v___x_357_);
lean_ctor_set(v___x_91_, 2, v_v_351_);
lean_ctor_set(v___x_91_, 1, v_k_350_);
lean_ctor_set(v___x_91_, 0, v___x_355_);
v___x_359_ = v___x_91_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_k_350_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_v_351_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_r_349_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(2u);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v_impl_235_);
lean_ctor_set(v___x_91_, 3, v_r_349_);
lean_ctor_set(v___x_91_, 0, v___x_366_);
v___x_368_ = v___x_91_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_86_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_87_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_r_349_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_impl_235_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
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
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec_ref(v_cmp_81_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_k_82_);
lean_ctor_set(v___x_372_, 2, v_v_83_);
lean_ctor_set(v___x_372_, 3, v_t_84_);
lean_ctor_set(v___x_372_, 4, v_t_84_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(lean_object* v_items_373_, lean_object* v_cmp_374_, lean_object* v_n_375_, lean_object* v_j_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_zero_378_; uint8_t v_isZero_379_; 
v_zero_378_ = lean_unsigned_to_nat(0u);
v_isZero_379_ = lean_nat_dec_eq(v_j_376_, v_zero_378_);
if (v_isZero_379_ == 1)
{
lean_dec(v_j_376_);
lean_dec_ref(v_cmp_374_);
return v_a_377_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_fst_382_; lean_object* v_one_383_; lean_object* v_n_384_; lean_object* v___x_385_; 
v___x_380_ = lean_nat_sub(v_n_375_, v_j_376_);
v___x_381_ = lean_array_fget_borrowed(v_items_373_, v___x_380_);
v_fst_382_ = lean_ctor_get(v___x_381_, 0);
v_one_383_ = lean_unsigned_to_nat(1u);
v_n_384_ = lean_nat_sub(v_j_376_, v_one_383_);
lean_dec(v_j_376_);
lean_inc(v_fst_382_);
lean_inc_ref(v_cmp_374_);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_374_, v_fst_382_, v___x_380_, v_a_377_);
v_j_376_ = v_n_384_;
v_a_377_ = v___x_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg___boxed(lean_object* v_items_387_, lean_object* v_cmp_388_, lean_object* v_n_389_, lean_object* v_j_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_387_, v_cmp_388_, v_n_389_, v_j_390_, v_a_391_);
lean_dec(v_n_389_);
lean_dec_ref(v_items_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray___redArg(lean_object* v_cmp_393_, lean_object* v_items_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_indices_397_; lean_object* v___x_398_; 
v___x_395_ = lean_array_get_size(v_items_394_);
v___x_396_ = lean_box(1);
v_indices_397_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_394_, v_cmp_393_, v___x_395_, v___x_395_, v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_items_394_);
lean_ctor_set(v___x_398_, 1, v_indices_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_ofArray(lean_object* v_00_u03b1_399_, lean_object* v_00_u03b2_400_, lean_object* v_cmp_401_, lean_object* v_items_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lake_Toml_RBDict_ofArray___redArg(v_cmp_401_, v_items_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0(lean_object* v_00_u03b1_404_, lean_object* v_cmp_405_, lean_object* v_00_u03b2_406_, lean_object* v_k_407_, lean_object* v_v_408_, lean_object* v_t_409_, lean_object* v_hl_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_405_, v_k_407_, v_v_408_, v_t_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_items_414_, lean_object* v_cmp_415_, lean_object* v_n_416_, lean_object* v_j_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___redArg(v_items_414_, v_cmp_415_, v_n_416_, v_j_417_, v_a_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1___boxed(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_items_423_, lean_object* v_cmp_424_, lean_object* v_n_425_, lean_object* v_j_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lake_Toml_RBDict_ofArray_spec__1(v_00_u03b1_421_, v_00_u03b2_422_, v_items_423_, v_cmp_424_, v_n_425_, v_j_426_, v_a_427_, v_a_428_);
lean_dec(v_n_425_);
lean_dec_ref(v_items_423_);
return v_res_429_;
}
}
uint8_t l_Lake_Toml_RBDict_beq___redArg(lean_object* v_inst_430_, lean_object* v_self_431_, lean_object* v_other_432_){
_start:
{
lean_object* v_items_433_; lean_object* v_items_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_items_433_ = lean_ctor_get(v_self_431_, 0);
v_items_434_ = lean_ctor_get(v_other_432_, 0);
v___x_435_ = lean_array_get_size(v_items_433_);
v___x_436_ = lean_array_get_size(v_items_434_);
v___x_437_ = lean_nat_dec_eq(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec_ref(v_inst_430_);
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = l_Array_isEqvAux___redArg(v_items_433_, v_items_434_, v_inst_430_, v___x_435_);
return v___x_438_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_430_ = stack[0].m_obj;
lean_object* v_self_431_ = stack[1].m_obj;
lean_object* v_other_432_ = stack[2].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_430_, v_self_431_, v_other_432_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___redArg___boxed(lean_object* v_inst_440_, lean_object* v_self_441_, lean_object* v_other_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_440_, v_self_441_, v_other_442_);
lean_dec_ref(v_other_442_);
lean_dec_ref(v_self_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
uint8_t l_Lake_Toml_RBDict_beq(lean_object* v_00_u03b1_445_, lean_object* v_00_u03b2_446_, lean_object* v_cmp_447_, lean_object* v_inst_448_, lean_object* v_self_449_, lean_object* v_other_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Lake_Toml_RBDict_beq___redArg(v_inst_448_, v_self_449_, v_other_450_);
return v___x_451_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_447_ = stack[2].m_obj;
lean_object* v_inst_448_ = stack[3].m_obj;
lean_object* v_self_449_ = stack[4].m_obj;
lean_object* v_other_450_ = stack[5].m_obj;
uint8_t v_res_452_;
v_res_452_ = l_Lake_Toml_RBDict_beq(lean_box(0), lean_box(0), v_cmp_447_, v_inst_448_, v_self_449_, v_other_450_);
stack->m_num = v_res_452_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___boxed(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_cmp_455_, lean_object* v_inst_456_, lean_object* v_self_457_, lean_object* v_other_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Lake_Toml_RBDict_beq(v_00_u03b1_453_, v_00_u03b2_454_, v_cmp_455_, v_inst_456_, v_self_457_, v_other_458_);
lean_dec_ref(v_other_458_);
lean_dec_ref(v_self_457_);
lean_dec_ref(v_cmp_455_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd___redArg(lean_object* v_cmp_461_, lean_object* v_inst_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_beq___boxed), 6, 4);
lean_closure_set(v___x_463_, 0, lean_box(0));
lean_closure_set(v___x_463_, 1, lean_box(0));
lean_closure_set(v___x_463_, 2, v_cmp_461_);
lean_closure_set(v___x_463_, 3, v_inst_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instBEqOfProd(lean_object* v_00_u03b1_464_, lean_object* v_00_u03b2_465_, lean_object* v_cmp_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_beq___boxed), 6, 4);
lean_closure_set(v___x_468_, 0, lean_box(0));
lean_closure_set(v___x_468_, 1, lean_box(0));
lean_closure_set(v___x_468_, 2, v_cmp_466_);
lean_closure_set(v___x_468_, 3, v_inst_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg(lean_object* v_t_469_){
_start:
{
lean_object* v_items_470_; lean_object* v___x_471_; 
v_items_470_ = lean_ctor_get(v_t_469_, 0);
v___x_471_ = lean_array_get_size(v_items_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___redArg___boxed(lean_object* v_t_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lake_Toml_RBDict_size___redArg(v_t_472_);
lean_dec_ref(v_t_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size(lean_object* v_00_u03b1_474_, lean_object* v_00_u03b2_475_, lean_object* v_cmp_476_, lean_object* v_t_477_){
_start:
{
lean_object* v_items_478_; lean_object* v___x_479_; 
v_items_478_ = lean_ctor_get(v_t_477_, 0);
v___x_479_ = lean_array_get_size(v_items_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_size___boxed(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_cmp_482_, lean_object* v_t_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lake_Toml_RBDict_size(v_00_u03b1_480_, v_00_u03b2_481_, v_cmp_482_, v_t_483_);
lean_dec_ref(v_t_483_);
lean_dec_ref(v_cmp_482_);
return v_res_484_;
}
}
uint8_t l_Lake_Toml_RBDict_isEmpty___redArg(lean_object* v_t_485_){
_start:
{
lean_object* v_items_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_items_486_ = lean_ctor_get(v_t_485_, 0);
v___x_487_ = lean_array_get_size(v_items_486_);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_nat_dec_eq(v___x_487_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_485_ = stack[0].m_obj;
uint8_t v_res_490_;
v_res_490_ = l_Lake_Toml_RBDict_isEmpty___redArg(v_t_485_);
stack->m_num = v_res_490_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___redArg___boxed(lean_object* v_t_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Lake_Toml_RBDict_isEmpty___redArg(v_t_491_);
lean_dec_ref(v_t_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
uint8_t l_Lake_Toml_RBDict_isEmpty(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_cmp_496_, lean_object* v_t_497_){
_start:
{
lean_object* v_items_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_items_498_ = lean_ctor_get(v_t_497_, 0);
v___x_499_ = lean_array_get_size(v_items_498_);
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_496_ = stack[2].m_obj;
lean_object* v_t_497_ = stack[3].m_obj;
uint8_t v_res_502_;
v_res_502_ = l_Lake_Toml_RBDict_isEmpty(lean_box(0), lean_box(0), v_cmp_496_, v_t_497_);
stack->m_num = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_isEmpty___boxed(lean_object* v_00_u03b1_503_, lean_object* v_00_u03b2_504_, lean_object* v_cmp_505_, lean_object* v_t_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l_Lake_Toml_RBDict_isEmpty(v_00_u03b1_503_, v_00_u03b2_504_, v_cmp_505_, v_t_506_);
lean_dec_ref(v_t_506_);
lean_dec_ref(v_cmp_505_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(size_t v_sz_509_, size_t v_i_510_, lean_object* v_bs_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_510_, v_sz_509_);
if (v___x_512_ == 0)
{
return v_bs_511_;
}
else
{
lean_object* v_v_513_; lean_object* v_fst_514_; lean_object* v___x_515_; lean_object* v_bs_x27_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; 
v_v_513_ = lean_array_uget_borrowed(v_bs_511_, v_i_510_);
v_fst_514_ = lean_ctor_get(v_v_513_, 0);
lean_inc(v_fst_514_);
v___x_515_ = lean_unsigned_to_nat(0u);
v_bs_x27_516_ = lean_array_uset(v_bs_511_, v_i_510_, v___x_515_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_510_, v___x_517_);
v___x_519_ = lean_array_uset(v_bs_x27_516_, v_i_510_, v_fst_514_);
v_i_510_ = v___x_518_;
v_bs_511_ = v___x_519_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_509_ = stack[0].m_num;
size_t v_i_510_ = stack[1].m_num;
lean_object* v_bs_511_ = stack[2].m_obj;
lean_object* v_res_521_;
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_509_, v_i_510_, v_bs_511_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg___boxed(lean_object* v_sz_522_, lean_object* v_i_523_, lean_object* v_bs_524_){
_start:
{
size_t v_sz_boxed_525_; size_t v_i_boxed_526_; lean_object* v_res_527_; 
v_sz_boxed_525_ = lean_unbox_usize(v_sz_522_);
lean_dec(v_sz_522_);
v_i_boxed_526_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_boxed_525_, v_i_boxed_526_, v_bs_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___redArg(lean_object* v_t_528_){
_start:
{
lean_object* v_items_529_; size_t v_sz_530_; size_t v___x_531_; lean_object* v___x_532_; 
v_items_529_ = lean_ctor_get(v_t_528_, 0);
lean_inc_ref(v_items_529_);
lean_dec_ref(v_t_528_);
v_sz_530_ = lean_array_size(v_items_529_);
v___x_531_ = ((size_t)0ULL);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_530_, v___x_531_, v_items_529_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys(lean_object* v_00_u03b1_533_, lean_object* v_00_u03b2_534_, lean_object* v_cmp_535_, lean_object* v_t_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lake_Toml_RBDict_keys___redArg(v_t_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_keys___boxed(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_cmp_540_, lean_object* v_t_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lake_Toml_RBDict_keys(v_00_u03b1_538_, v_00_u03b2_539_, v_cmp_540_, v_t_541_);
lean_dec_ref(v_cmp_540_);
return v_res_542_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, size_t v_sz_545_, size_t v_i_546_, lean_object* v_bs_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___redArg(v_sz_545_, v_i_546_, v_bs_547_);
return v___x_548_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_545_ = stack[2].m_num;
size_t v_i_546_ = stack[3].m_num;
lean_object* v_bs_547_ = stack[4].m_obj;
lean_object* v_res_549_;
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(lean_box(0), lean_box(0), v_sz_545_, v_i_546_, v_bs_547_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0___boxed(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_sz_552_, lean_object* v_i_553_, lean_object* v_bs_554_){
_start:
{
size_t v_sz_boxed_555_; size_t v_i_boxed_556_; lean_object* v_res_557_; 
v_sz_boxed_555_ = lean_unbox_usize(v_sz_552_);
lean_dec(v_sz_552_);
v_i_boxed_556_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_keys_spec__0(v_00_u03b1_550_, v_00_u03b2_551_, v_sz_boxed_555_, v_i_boxed_556_, v_bs_554_);
return v_res_557_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(size_t v_sz_558_, size_t v_i_559_, lean_object* v_bs_560_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_lt(v_i_559_, v_sz_558_);
if (v___x_561_ == 0)
{
return v_bs_560_;
}
else
{
lean_object* v_v_562_; lean_object* v_snd_563_; lean_object* v___x_564_; lean_object* v_bs_x27_565_; size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; 
v_v_562_ = lean_array_uget_borrowed(v_bs_560_, v_i_559_);
v_snd_563_ = lean_ctor_get(v_v_562_, 1);
lean_inc(v_snd_563_);
v___x_564_ = lean_unsigned_to_nat(0u);
v_bs_x27_565_ = lean_array_uset(v_bs_560_, v_i_559_, v___x_564_);
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_i_559_, v___x_566_);
v___x_568_ = lean_array_uset(v_bs_x27_565_, v_i_559_, v_snd_563_);
v_i_559_ = v___x_567_;
v_bs_560_ = v___x_568_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_558_ = stack[0].m_num;
size_t v_i_559_ = stack[1].m_num;
lean_object* v_bs_560_ = stack[2].m_obj;
lean_object* v_res_570_;
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_558_, v_i_559_, v_bs_560_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg___boxed(lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_bs_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_575_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_boxed_574_, v_i_boxed_575_, v_bs_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___redArg(lean_object* v_t_577_){
_start:
{
lean_object* v_items_578_; size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; 
v_items_578_ = lean_ctor_get(v_t_577_, 0);
lean_inc_ref(v_items_578_);
lean_dec_ref(v_t_577_);
v_sz_579_ = lean_array_size(v_items_578_);
v___x_580_ = ((size_t)0ULL);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_579_, v___x_580_, v_items_578_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_cmp_584_, lean_object* v_t_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lake_Toml_RBDict_values___redArg(v_t_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_values___boxed(lean_object* v_00_u03b1_587_, lean_object* v_00_u03b2_588_, lean_object* v_cmp_589_, lean_object* v_t_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lake_Toml_RBDict_values(v_00_u03b1_587_, v_00_u03b2_588_, v_cmp_589_, v_t_590_);
lean_dec_ref(v_cmp_589_);
return v_res_591_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b2_593_, size_t v_sz_594_, size_t v_i_595_, lean_object* v_bs_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___redArg(v_sz_594_, v_i_595_, v_bs_596_);
return v___x_597_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_594_ = stack[2].m_num;
size_t v_i_595_ = stack[3].m_num;
lean_object* v_bs_596_ = stack[4].m_obj;
lean_object* v_res_598_;
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(lean_box(0), lean_box(0), v_sz_594_, v_i_595_, v_bs_596_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0___boxed(lean_object* v_00_u03b1_599_, lean_object* v_00_u03b2_600_, lean_object* v_sz_601_, lean_object* v_i_602_, lean_object* v_bs_603_){
_start:
{
size_t v_sz_boxed_604_; size_t v_i_boxed_605_; lean_object* v_res_606_; 
v_sz_boxed_604_ = lean_unbox_usize(v_sz_601_);
lean_dec(v_sz_601_);
v_i_boxed_605_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_res_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_Toml_RBDict_values_spec__0(v_00_u03b1_599_, v_00_u03b2_600_, v_sz_boxed_604_, v_i_boxed_605_, v_bs_603_);
return v_res_606_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(lean_object* v_cmp_607_, lean_object* v_k_608_, lean_object* v_t_609_){
_start:
{
if (lean_obj_tag(v_t_609_) == 0)
{
lean_object* v_k_610_; lean_object* v_l_611_; lean_object* v_r_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_k_610_ = lean_ctor_get(v_t_609_, 1);
lean_inc(v_k_610_);
v_l_611_ = lean_ctor_get(v_t_609_, 3);
lean_inc(v_l_611_);
v_r_612_ = lean_ctor_get(v_t_609_, 4);
lean_inc(v_r_612_);
lean_dec_ref_known(v_t_609_, 5);
lean_inc_ref(v_cmp_607_);
lean_inc(v_k_608_);
v___x_613_ = lean_apply_2(v_cmp_607_, v_k_608_, v_k_610_);
v___x_614_ = lean_unbox(v___x_613_);
switch(v___x_614_)
{
case 0:
{
lean_dec(v_r_612_);
v_t_609_ = v_l_611_;
goto _start;
}
case 1:
{
uint8_t v___x_616_; 
lean_dec(v_r_612_);
lean_dec(v_l_611_);
lean_dec(v_k_608_);
lean_dec_ref(v_cmp_607_);
v___x_616_ = 1;
return v___x_616_;
}
default: 
{
lean_dec(v_l_611_);
v_t_609_ = v_r_612_;
goto _start;
}
}
}
else
{
uint8_t v___x_618_; 
lean_dec(v_k_608_);
lean_dec_ref(v_cmp_607_);
v___x_618_ = 0;
return v___x_618_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_607_ = stack[0].m_obj;
lean_object* v_k_608_ = stack[1].m_obj;
lean_object* v_t_609_ = stack[2].m_obj;
uint8_t v_res_619_;
v_res_619_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_607_, v_k_608_, v_t_609_);
stack->m_num = v_res_619_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg___boxed(lean_object* v_cmp_620_, lean_object* v_k_621_, lean_object* v_t_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_620_, v_k_621_, v_t_622_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object* v_cmp_625_, lean_object* v_k_626_, lean_object* v_t_627_){
_start:
{
lean_object* v_indices_628_; uint8_t v___x_629_; 
v_indices_628_ = lean_ctor_get(v_t_627_, 1);
lean_inc(v_indices_628_);
lean_dec_ref(v_t_627_);
v___x_629_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_625_, v_k_626_, v_indices_628_);
return v___x_629_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_625_ = stack[0].m_obj;
lean_object* v_k_626_ = stack[1].m_obj;
lean_object* v_t_627_ = stack[2].m_obj;
uint8_t v_res_630_;
v_res_630_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_625_, v_k_626_, v_t_627_);
stack->m_num = v_res_630_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___redArg___boxed(lean_object* v_cmp_631_, lean_object* v_k_632_, lean_object* v_t_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_631_, v_k_632_, v_t_633_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
uint8_t l_Lake_Toml_RBDict_contains(lean_object* v_00_u03b1_636_, lean_object* v_00_u03b2_637_, lean_object* v_cmp_638_, lean_object* v_k_639_, lean_object* v_t_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Lake_Toml_RBDict_contains___redArg(v_cmp_638_, v_k_639_, v_t_640_);
return v___x_641_;
}
}
LEAN_EXPORT void l_Lake_Toml_RBDict_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_638_ = stack[2].m_obj;
lean_object* v_k_639_ = stack[3].m_obj;
lean_object* v_t_640_ = stack[4].m_obj;
uint8_t v_res_642_;
v_res_642_ = l_Lake_Toml_RBDict_contains(lean_box(0), lean_box(0), v_cmp_638_, v_k_639_, v_t_640_);
stack->m_num = v_res_642_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_contains___boxed(lean_object* v_00_u03b1_643_, lean_object* v_00_u03b2_644_, lean_object* v_cmp_645_, lean_object* v_k_646_, lean_object* v_t_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Lake_Toml_RBDict_contains(v_00_u03b1_643_, v_00_u03b2_644_, v_cmp_645_, v_k_646_, v_t_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(lean_object* v_00_u03b1_650_, lean_object* v_cmp_651_, lean_object* v_00_u03b2_652_, lean_object* v_k_653_, lean_object* v_t_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___redArg(v_cmp_651_, v_k_653_, v_t_654_);
return v___x_655_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_651_ = stack[1].m_obj;
lean_object* v_k_653_ = stack[3].m_obj;
lean_object* v_t_654_ = stack[4].m_obj;
uint8_t v_res_656_;
v_res_656_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(lean_box(0), v_cmp_651_, lean_box(0), v_k_653_, v_t_654_);
stack->m_num = v_res_656_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0___boxed(lean_object* v_00_u03b1_657_, lean_object* v_cmp_658_, lean_object* v_00_u03b2_659_, lean_object* v_k_660_, lean_object* v_t_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_Toml_RBDict_contains_spec__0(v_00_u03b1_657_, v_cmp_658_, v_00_u03b2_659_, v_k_660_, v_t_661_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(lean_object* v_cmp_664_, lean_object* v_t_665_, lean_object* v_k_666_){
_start:
{
if (lean_obj_tag(v_t_665_) == 0)
{
lean_object* v_k_667_; lean_object* v_v_668_; lean_object* v_l_669_; lean_object* v_r_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_k_667_ = lean_ctor_get(v_t_665_, 1);
lean_inc(v_k_667_);
v_v_668_ = lean_ctor_get(v_t_665_, 2);
lean_inc(v_v_668_);
v_l_669_ = lean_ctor_get(v_t_665_, 3);
lean_inc(v_l_669_);
v_r_670_ = lean_ctor_get(v_t_665_, 4);
lean_inc(v_r_670_);
lean_dec_ref_known(v_t_665_, 5);
lean_inc_ref(v_cmp_664_);
lean_inc(v_k_666_);
v___x_671_ = lean_apply_2(v_cmp_664_, v_k_666_, v_k_667_);
v___x_672_ = lean_unbox(v___x_671_);
switch(v___x_672_)
{
case 0:
{
lean_dec(v_r_670_);
lean_dec(v_v_668_);
v_t_665_ = v_l_669_;
goto _start;
}
case 1:
{
lean_object* v___x_674_; 
lean_dec(v_r_670_);
lean_dec(v_l_669_);
lean_dec(v_k_666_);
lean_dec_ref(v_cmp_664_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_v_668_);
return v___x_674_;
}
default: 
{
lean_dec(v_l_669_);
lean_dec(v_v_668_);
v_t_665_ = v_r_670_;
goto _start;
}
}
}
else
{
lean_object* v___x_676_; 
lean_dec(v_k_666_);
lean_dec_ref(v_cmp_664_);
v___x_676_ = lean_box(0);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f___redArg(lean_object* v_cmp_677_, lean_object* v_k_678_, lean_object* v_t_679_){
_start:
{
lean_object* v_items_680_; lean_object* v_indices_681_; lean_object* v___x_682_; 
v_items_680_ = lean_ctor_get(v_t_679_, 0);
lean_inc_ref(v_items_680_);
v_indices_681_ = lean_ctor_get(v_t_679_, 1);
lean_inc(v_indices_681_);
lean_dec_ref(v_t_679_);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_677_, v_indices_681_, v_k_678_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v___x_683_; 
lean_dec_ref(v_items_680_);
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_694_; 
v_val_684_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_694_ == 0)
{
v___x_686_ = v___x_682_;
v_isShared_687_ = v_isSharedCheck_694_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v___x_682_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_694_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_array_get_size(v_items_680_);
lean_dec_ref(v_items_680_);
v___x_689_ = lean_nat_dec_lt(v_val_684_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
lean_del_object(v___x_686_);
lean_dec(v_val_684_);
v___x_690_ = lean_box(0);
return v___x_690_;
}
else
{
lean_object* v___x_692_; 
if (v_isShared_687_ == 0)
{
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_val_684_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findIdx_x3f(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_cmp_697_, lean_object* v_k_698_, lean_object* v_t_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_697_, v_k_698_, v_t_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0(lean_object* v_00_u03b1_701_, lean_object* v_cmp_702_, lean_object* v_00_u03b4_703_, lean_object* v_t_704_, lean_object* v_k_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_Toml_RBDict_findIdx_x3f_spec__0___redArg(v_cmp_702_, v_t_704_, v_k_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object* v_cmp_707_, lean_object* v_k_708_, lean_object* v_t_709_){
_start:
{
lean_object* v___x_710_; 
lean_inc_ref(v_t_709_);
v___x_710_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_707_, v_k_708_, v_t_709_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v___x_711_; 
lean_dec_ref(v_t_709_);
v___x_711_ = lean_box(0);
return v___x_711_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_721_; 
v_val_712_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_721_ == 0)
{
v___x_714_ = v___x_710_;
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v___x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_items_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v_items_716_ = lean_ctor_get(v_t_709_, 0);
lean_inc_ref(v_items_716_);
lean_dec_ref(v_t_709_);
v___x_717_ = lean_array_fget(v_items_716_, v_val_712_);
lean_dec(v_val_712_);
lean_dec_ref(v_items_716_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_findEntry_x3f(lean_object* v_00_u03b1_722_, lean_object* v_00_u03b2_723_, lean_object* v_cmp_724_, lean_object* v_k_725_, lean_object* v_t_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_724_, v_k_725_, v_t_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f___redArg(lean_object* v_cmp_728_, lean_object* v_k_729_, lean_object* v_t_730_){
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
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_find_x3f(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_cmp_744_, lean_object* v_k_745_, lean_object* v_t_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v_cmp_744_, v_k_745_, v_t_746_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_box(0);
return v___x_748_;
}
else
{
lean_object* v_val_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_757_; 
v_val_749_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_757_ == 0)
{
v___x_751_ = v___x_747_;
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_val_749_);
lean_dec(v___x_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_757_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_snd_753_; lean_object* v___x_755_; 
v_snd_753_ = lean_ctor_get(v_val_749_, 1);
lean_inc(v_snd_753_);
lean_dec(v_val_749_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v_snd_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_snd_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object* v_cmp_758_, lean_object* v_k_759_, lean_object* v_v_760_, lean_object* v_t_761_){
_start:
{
lean_object* v_items_762_; lean_object* v_indices_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_774_; 
v_items_762_ = lean_ctor_get(v_t_761_, 0);
v_indices_763_ = lean_ctor_get(v_t_761_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_t_761_);
if (v_isSharedCheck_774_ == 0)
{
v___x_765_ = v_t_761_;
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_indices_763_);
lean_inc(v_items_762_);
lean_dec(v_t_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_774_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_inc(v_k_759_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_k_759_);
lean_ctor_set(v___x_767_, 1, v_v_760_);
lean_inc_ref(v_items_762_);
v___x_768_ = lean_array_push(v_items_762_, v___x_767_);
v___x_769_ = lean_array_get_size(v_items_762_);
lean_dec_ref(v_items_762_);
v___x_770_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Toml_RBDict_ofArray_spec__0___redArg(v_cmp_758_, v_k_759_, v___x_769_, v_indices_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_770_);
lean_ctor_set(v___x_765_, 0, v___x_768_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_push(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_cmp_777_, lean_object* v_k_778_, lean_object* v_v_779_, lean_object* v_t_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_777_, v_k_778_, v_v_779_, v_t_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___redArg(lean_object* v_cmp_782_, lean_object* v_k_783_, lean_object* v_f_784_, lean_object* v_t_785_){
_start:
{
lean_object* v___x_786_; 
lean_inc_ref(v_t_785_);
lean_inc(v_k_783_);
lean_inc_ref(v_cmp_782_);
v___x_786_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_782_, v_k_783_, v_t_785_);
if (lean_obj_tag(v___x_786_) == 1)
{
lean_object* v_val_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_k_783_);
lean_dec_ref(v_cmp_782_);
v_val_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_822_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_822_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_val_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_822_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v_items_791_; lean_object* v_indices_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_821_; 
v_items_791_ = lean_ctor_get(v_t_785_, 0);
v_indices_792_ = lean_ctor_get(v_t_785_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_t_785_);
if (v_isSharedCheck_821_ == 0)
{
v___x_794_ = v_t_785_;
v_isShared_795_ = v_isSharedCheck_821_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_indices_792_);
lean_inc(v_items_791_);
lean_dec(v_t_785_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_821_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = lean_array_get_size(v_items_791_);
v___x_797_ = lean_nat_dec_lt(v_val_787_, v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_799_; 
lean_del_object(v___x_789_);
lean_dec(v_val_787_);
lean_dec(v_f_784_);
if (v_isShared_795_ == 0)
{
v___x_799_ = v___x_794_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_items_791_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_indices_792_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
lean_object* v_v_801_; lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_820_; 
v_v_801_ = lean_array_fget(v_items_791_, v_val_787_);
v_fst_802_ = lean_ctor_get(v_v_801_, 0);
v_snd_803_ = lean_ctor_get(v_v_801_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_v_801_);
if (v_isSharedCheck_820_ == 0)
{
v___x_805_ = v_v_801_;
v_isShared_806_ = v_isSharedCheck_820_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snd_803_);
lean_inc(v_fst_802_);
lean_dec(v_v_801_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_820_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v_xs_x27_808_; lean_object* v___x_810_; 
v___x_807_ = lean_box(0);
v_xs_x27_808_ = lean_array_fset(v_items_791_, v_val_787_, v___x_807_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_snd_803_);
v___x_810_ = v___x_789_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_snd_803_);
v___x_810_ = v_reuseFailAlloc_819_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_apply_1(v_f_784_, v___x_810_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_811_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_fst_802_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_818_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_array_fset(v_xs_x27_808_, v_val_787_, v___x_813_);
lean_dec(v_val_787_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_814_);
v___x_816_ = v___x_794_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_indices_792_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
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
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v___x_786_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_apply_1(v_f_784_, v___x_823_);
v___x_825_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_782_, v_k_783_, v___x_824_, v_t_785_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_cmp_828_, lean_object* v_k_829_, lean_object* v_f_830_, lean_object* v_t_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lake_Toml_RBDict_alter___redArg(v_cmp_828_, v_k_829_, v_f_830_, v_t_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert___redArg(lean_object* v_cmp_833_, lean_object* v_k_834_, lean_object* v_v_835_, lean_object* v_t_836_){
_start:
{
lean_object* v___x_837_; 
lean_inc_ref(v_t_836_);
lean_inc(v_k_834_);
lean_inc_ref(v_cmp_833_);
v___x_837_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v_cmp_833_, v_k_834_, v_t_836_);
if (lean_obj_tag(v___x_837_) == 1)
{
lean_object* v_val_838_; lean_object* v_items_839_; lean_object* v_indices_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_val_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_val_838_);
lean_dec_ref_known(v___x_837_, 1);
v_items_839_ = lean_ctor_get(v_t_836_, 0);
v_indices_840_ = lean_ctor_get(v_t_836_, 1);
v___x_841_ = lean_array_get_size(v_items_839_);
v___x_842_ = lean_nat_dec_lt(v_val_838_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v_val_838_);
v___x_843_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_833_, v_k_834_, v_v_835_, v_t_836_);
return v___x_843_;
}
else
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_852_; 
lean_inc(v_indices_840_);
lean_inc_ref(v_items_839_);
lean_dec_ref(v_cmp_833_);
v_isSharedCheck_852_ = !lean_is_exclusive(v_t_836_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; lean_object* v_unused_854_; 
v_unused_853_ = lean_ctor_get(v_t_836_, 1);
lean_dec(v_unused_853_);
v_unused_854_ = lean_ctor_get(v_t_836_, 0);
lean_dec(v_unused_854_);
v___x_845_ = v_t_836_;
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_t_836_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_k_834_);
lean_ctor_set(v___x_847_, 1, v_v_835_);
v___x_848_ = lean_array_fset(v_items_839_, v_val_838_, v___x_847_);
lean_dec(v_val_838_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_848_);
v___x_850_ = v___x_845_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_indices_840_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v___x_855_; 
lean_dec(v___x_837_);
v___x_855_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_833_, v_k_834_, v_v_835_, v_t_836_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_insert(lean_object* v_00_u03b1_856_, lean_object* v_00_u03b2_857_, lean_object* v_cmp_858_, lean_object* v_k_859_, lean_object* v_v_860_, lean_object* v_t_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_858_, v_k_859_, v_v_860_, v_t_861_);
return v___x_862_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(lean_object* v_cmp_863_, lean_object* v_as_864_, size_t v_i_865_, size_t v_stop_866_, lean_object* v_b_867_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_eq(v_i_865_, v_stop_866_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v_fst_870_; lean_object* v_snd_871_; lean_object* v___x_872_; size_t v___x_873_; size_t v___x_874_; 
v___x_869_ = lean_array_uget_borrowed(v_as_864_, v_i_865_);
v_fst_870_ = lean_ctor_get(v___x_869_, 0);
v_snd_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc(v_snd_871_);
lean_inc(v_fst_870_);
lean_inc_ref(v_cmp_863_);
v___x_872_ = l_Lake_Toml_RBDict_insert___redArg(v_cmp_863_, v_fst_870_, v_snd_871_, v_b_867_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_865_, v___x_873_);
v_i_865_ = v___x_874_;
v_b_867_ = v___x_872_;
goto _start;
}
else
{
lean_dec_ref(v_cmp_863_);
return v_b_867_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_863_ = stack[0].m_obj;
lean_object* v_as_864_ = stack[1].m_obj;
size_t v_i_865_ = stack[2].m_num;
size_t v_stop_866_ = stack[3].m_num;
lean_object* v_b_867_ = stack[4].m_obj;
lean_object* v_res_876_;
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_863_, v_as_864_, v_i_865_, v_stop_866_, v_b_867_);
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg___boxed(lean_object* v_cmp_877_, lean_object* v_as_878_, lean_object* v_i_879_, lean_object* v_stop_880_, lean_object* v_b_881_){
_start:
{
size_t v_i_boxed_882_; size_t v_stop_boxed_883_; lean_object* v_res_884_; 
v_i_boxed_882_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_stop_boxed_883_ = lean_unbox_usize(v_stop_880_);
lean_dec(v_stop_880_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_877_, v_as_878_, v_i_boxed_882_, v_stop_boxed_883_, v_b_881_);
lean_dec_ref(v_as_878_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg(lean_object* v_cmp_885_, lean_object* v_self_886_, lean_object* v_other_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_array_get_size(v_other_887_);
v___x_890_ = lean_nat_dec_lt(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec_ref(v_cmp_885_);
return v_self_886_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = lean_nat_dec_le(v___x_889_, v___x_889_);
if (v___x_891_ == 0)
{
if (v___x_890_ == 0)
{
lean_dec_ref(v_cmp_885_);
return v_self_886_;
}
else
{
size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_892_ = ((size_t)0ULL);
v___x_893_ = lean_usize_of_nat(v___x_889_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_885_, v_other_887_, v___x_892_, v___x_893_, v_self_886_);
return v___x_894_;
}
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_889_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_885_, v_other_887_, v___x_895_, v___x_896_, v_self_886_);
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___redArg___boxed(lean_object* v_cmp_898_, lean_object* v_self_899_, lean_object* v_other_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_898_, v_self_899_, v_other_900_);
lean_dec_ref(v_other_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_cmp_904_, lean_object* v_self_905_, lean_object* v_other_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_904_, v_self_905_, v_other_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_appendArray___boxed(lean_object* v_00_u03b1_908_, lean_object* v_00_u03b2_909_, lean_object* v_cmp_910_, lean_object* v_self_911_, lean_object* v_other_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lake_Toml_RBDict_appendArray(v_00_u03b1_908_, v_00_u03b2_909_, v_cmp_910_, v_self_911_, v_other_912_);
lean_dec_ref(v_other_912_);
return v_res_913_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_cmp_916_, lean_object* v_as_917_, size_t v_i_918_, size_t v_stop_919_, lean_object* v_b_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___redArg(v_cmp_916_, v_as_917_, v_i_918_, v_stop_919_, v_b_920_);
return v___x_921_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_916_ = stack[2].m_obj;
lean_object* v_as_917_ = stack[3].m_obj;
size_t v_i_918_ = stack[4].m_num;
size_t v_stop_919_ = stack[5].m_num;
lean_object* v_b_920_ = stack[6].m_obj;
lean_object* v_res_922_;
v_res_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(lean_box(0), lean_box(0), v_cmp_916_, v_as_917_, v_i_918_, v_stop_919_, v_b_920_);
stack->m_obj
 = v_res_922_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0___boxed(lean_object* v_00_u03b1_923_, lean_object* v_00_u03b2_924_, lean_object* v_cmp_925_, lean_object* v_as_926_, lean_object* v_i_927_, lean_object* v_stop_928_, lean_object* v_b_929_){
_start:
{
size_t v_i_boxed_930_; size_t v_stop_boxed_931_; lean_object* v_res_932_; 
v_i_boxed_930_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_stop_boxed_931_ = lean_unbox_usize(v_stop_928_);
lean_dec(v_stop_928_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Toml_RBDict_appendArray_spec__0(v_00_u03b1_923_, v_00_u03b2_924_, v_cmp_925_, v_as_926_, v_i_boxed_930_, v_stop_boxed_931_, v_b_929_);
lean_dec_ref(v_as_926_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd___redArg(lean_object* v_cmp_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_appendArray___boxed), 5, 3);
lean_closure_set(v___x_934_, 0, lean_box(0));
lean_closure_set(v___x_934_, 1, lean_box(0));
lean_closure_set(v___x_934_, 2, v_cmp_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instHAppendArrayProd(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_cmp_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_appendArray___boxed), 5, 3);
lean_closure_set(v___x_938_, 0, lean_box(0));
lean_closure_set(v___x_938_, 1, lean_box(0));
lean_closure_set(v___x_938_, 2, v_cmp_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg(lean_object* v_cmp_939_, lean_object* v_self_940_, lean_object* v_other_941_){
_start:
{
lean_object* v_items_942_; lean_object* v___x_943_; 
v_items_942_ = lean_ctor_get(v_other_941_, 0);
v___x_943_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_939_, v_self_940_, v_items_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___redArg___boxed(lean_object* v_cmp_944_, lean_object* v_self_945_, lean_object* v_other_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lake_Toml_RBDict_append___redArg(v_cmp_944_, v_self_945_, v_other_946_);
lean_dec_ref(v_other_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append(lean_object* v_00_u03b1_948_, lean_object* v_00_u03b2_949_, lean_object* v_cmp_950_, lean_object* v_self_951_, lean_object* v_other_952_){
_start:
{
lean_object* v_items_953_; lean_object* v___x_954_; 
v_items_953_ = lean_ctor_get(v_other_952_, 0);
v___x_954_ = l_Lake_Toml_RBDict_appendArray___redArg(v_cmp_950_, v_self_951_, v_items_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_append___boxed(lean_object* v_00_u03b1_955_, lean_object* v_00_u03b2_956_, lean_object* v_cmp_957_, lean_object* v_self_958_, lean_object* v_other_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lake_Toml_RBDict_append(v_00_u03b1_955_, v_00_u03b2_956_, v_cmp_957_, v_self_958_, v_other_959_);
lean_dec_ref(v_other_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend___redArg(lean_object* v_cmp_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_append___boxed), 5, 3);
lean_closure_set(v___x_962_, 0, lean_box(0));
lean_closure_set(v___x_962_, 1, lean_box(0));
lean_closure_set(v___x_962_, 2, v_cmp_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_instAppend(lean_object* v_00_u03b1_963_, lean_object* v_00_u03b2_964_, lean_object* v_cmp_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_append___boxed), 5, 3);
lean_closure_set(v___x_966_, 0, lean_box(0));
lean_closure_set(v___x_966_, 1, lean_box(0));
lean_closure_set(v___x_966_, 2, v_cmp_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg___lam__0(lean_object* v_f_967_, lean_object* v_x_968_){
_start:
{
lean_object* v_fst_969_; lean_object* v_snd_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_fst_969_ = lean_ctor_get(v_x_968_, 0);
v_snd_970_ = lean_ctor_get(v_x_968_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v_x_968_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_snd_970_);
lean_inc(v_fst_969_);
lean_dec(v_x_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
lean_inc(v_fst_969_);
v___x_974_ = lean_apply_2(v_f_967_, v_fst_969_, v_snd_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_fst_969_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___redArg(lean_object* v_f_998_, lean_object* v_t_999_){
_start:
{
lean_object* v_items_1000_; lean_object* v_indices_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1013_; 
v_items_1000_ = lean_ctor_get(v_t_999_, 0);
v_indices_1001_ = lean_ctor_get(v_t_999_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_t_999_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1003_ = v_t_999_;
v_isShared_1004_ = v_isSharedCheck_1013_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_indices_1001_);
lean_inc(v_items_1000_);
lean_dec(v_t_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1013_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___f_1005_; lean_object* v___x_1006_; size_t v_sz_1007_; size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___f_1005_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1005_, 0, v_f_998_);
v___x_1006_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_sz_1007_ = lean_array_size(v_items_1000_);
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1006_, v___f_1005_, v_sz_1007_, v___x_1008_, v_items_1000_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1009_);
v___x_1011_ = v___x_1003_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_indices_1001_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_00_u03b3_1016_, lean_object* v_cmp_1017_, lean_object* v_f_1018_, lean_object* v_t_1019_){
_start:
{
lean_object* v_items_1020_; lean_object* v_indices_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1033_; 
v_items_1020_ = lean_ctor_get(v_t_1019_, 0);
v_indices_1021_ = lean_ctor_get(v_t_1019_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_t_1019_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1023_ = v_t_1019_;
v_isShared_1024_ = v_isSharedCheck_1033_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_indices_1021_);
lean_inc(v_items_1020_);
lean_dec(v_t_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1033_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___f_1025_; lean_object* v___x_1026_; size_t v_sz_1027_; size_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___f_1025_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1025_, 0, v_f_1018_);
v___x_1026_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_sz_1027_ = lean_array_size(v_items_1020_);
v___x_1028_ = ((size_t)0ULL);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1026_, v___f_1025_, v_sz_1027_, v___x_1028_, v_items_1020_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1029_);
v___x_1031_ = v___x_1023_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_indices_1021_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_map___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_00_u03b3_1036_, lean_object* v_cmp_1037_, lean_object* v_f_1038_, lean_object* v_t_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lake_Toml_RBDict_map(v_00_u03b1_1034_, v_00_u03b2_1035_, v_00_u03b3_1036_, v_cmp_1037_, v_f_1038_, v_t_1039_);
lean_dec_ref(v_cmp_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg___lam__0(lean_object* v_p_1041_, lean_object* v_cmp_1042_, lean_object* v_x1_1043_, lean_object* v_x2_1044_){
_start:
{
lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_fst_1045_ = lean_ctor_get(v_x2_1044_, 0);
lean_inc_n(v_fst_1045_, 2);
v_snd_1046_ = lean_ctor_get(v_x2_1044_, 1);
lean_inc_n(v_snd_1046_, 2);
lean_dec_ref(v_x2_1044_);
v___x_1047_ = lean_apply_2(v_p_1041_, v_fst_1045_, v_snd_1046_);
v___x_1048_ = lean_unbox(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v_snd_1046_);
lean_dec(v_fst_1045_);
lean_dec_ref(v_cmp_1042_);
return v_x1_1043_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1042_, v_fst_1045_, v_snd_1046_, v_x1_1043_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter___redArg(lean_object* v_cmp_1050_, lean_object* v_p_1051_, lean_object* v_t_1052_){
_start:
{
lean_object* v_items_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_items_1053_ = lean_ctor_get(v_t_1052_, 0);
lean_inc_ref(v_items_1053_);
lean_dec_ref(v_t_1052_);
v___x_1054_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_array_get_size(v_items_1053_);
v___x_1057_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1058_ = lean_nat_dec_lt(v___x_1055_, v___x_1056_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v_items_1053_);
lean_dec_ref(v_p_1051_);
lean_dec_ref(v_cmp_1050_);
return v___x_1054_;
}
else
{
lean_object* v___f_1059_; uint8_t v___x_1060_; 
v___f_1059_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filter___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1059_, 0, v_p_1051_);
lean_closure_set(v___f_1059_, 1, v_cmp_1050_);
v___x_1060_ = lean_nat_dec_le(v___x_1056_, v___x_1056_);
if (v___x_1060_ == 0)
{
if (v___x_1058_ == 0)
{
lean_dec_ref(v___f_1059_);
lean_dec_ref(v_items_1053_);
return v___x_1054_;
}
else
{
size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = ((size_t)0ULL);
v___x_1062_ = lean_usize_of_nat(v___x_1056_);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1057_, v___f_1059_, v_items_1053_, v___x_1061_, v___x_1062_, v___x_1054_);
return v___x_1063_;
}
}
else
{
size_t v___x_1064_; size_t v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = ((size_t)0ULL);
v___x_1065_ = lean_usize_of_nat(v___x_1056_);
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1057_, v___f_1059_, v_items_1053_, v___x_1064_, v___x_1065_, v___x_1054_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filter(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_cmp_1069_, lean_object* v_p_1070_, lean_object* v_t_1071_){
_start:
{
lean_object* v_items_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_items_1072_ = lean_ctor_get(v_t_1071_, 0);
lean_inc_ref(v_items_1072_);
lean_dec_ref(v_t_1071_);
v___x_1073_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_array_get_size(v_items_1072_);
v___x_1076_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1077_ = lean_nat_dec_lt(v___x_1074_, v___x_1075_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v_items_1072_);
lean_dec_ref(v_p_1070_);
lean_dec_ref(v_cmp_1069_);
return v___x_1073_;
}
else
{
lean_object* v___f_1078_; uint8_t v___x_1079_; 
v___f_1078_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filter___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1078_, 0, v_p_1070_);
lean_closure_set(v___f_1078_, 1, v_cmp_1069_);
v___x_1079_ = lean_nat_dec_le(v___x_1075_, v___x_1075_);
if (v___x_1079_ == 0)
{
if (v___x_1077_ == 0)
{
lean_dec_ref(v___f_1078_);
lean_dec_ref(v_items_1072_);
return v___x_1073_;
}
else
{
size_t v___x_1080_; size_t v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = ((size_t)0ULL);
v___x_1081_ = lean_usize_of_nat(v___x_1075_);
v___x_1082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1076_, v___f_1078_, v_items_1072_, v___x_1080_, v___x_1081_, v___x_1073_);
return v___x_1082_;
}
}
else
{
size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = lean_usize_of_nat(v___x_1075_);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1076_, v___f_1078_, v_items_1072_, v___x_1083_, v___x_1084_, v___x_1073_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg___lam__0(lean_object* v_f_1086_, lean_object* v_cmp_1087_, lean_object* v_x1_1088_, lean_object* v_x2_1089_){
_start:
{
lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___x_1092_; 
v_fst_1090_ = lean_ctor_get(v_x2_1089_, 0);
lean_inc_n(v_fst_1090_, 2);
v_snd_1091_ = lean_ctor_get(v_x2_1089_, 1);
lean_inc(v_snd_1091_);
lean_dec_ref(v_x2_1089_);
v___x_1092_ = lean_apply_2(v_f_1086_, v_fst_1090_, v_snd_1091_);
if (lean_obj_tag(v___x_1092_) == 1)
{
lean_object* v_val_1093_; lean_object* v___x_1094_; 
v_val_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = l_Lake_Toml_RBDict_push___redArg(v_cmp_1087_, v_fst_1090_, v_val_1093_, v_x1_1088_);
return v___x_1094_;
}
else
{
lean_dec(v___x_1092_);
lean_dec(v_fst_1090_);
lean_dec_ref(v_cmp_1087_);
return v_x1_1088_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap___redArg(lean_object* v_cmp_1095_, lean_object* v_f_1096_, lean_object* v_t_1097_){
_start:
{
lean_object* v_items_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_items_1098_ = lean_ctor_get(v_t_1097_, 0);
lean_inc_ref(v_items_1098_);
lean_dec_ref(v_t_1097_);
v___x_1099_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_array_get_size(v_items_1098_);
v___x_1102_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1103_ = lean_nat_dec_lt(v___x_1100_, v___x_1101_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v_items_1098_);
lean_dec_ref(v_f_1096_);
lean_dec_ref(v_cmp_1095_);
return v___x_1099_;
}
else
{
lean_object* v___f_1104_; uint8_t v___x_1105_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filterMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1104_, 0, v_f_1096_);
lean_closure_set(v___f_1104_, 1, v_cmp_1095_);
v___x_1105_ = lean_nat_dec_le(v___x_1101_, v___x_1101_);
if (v___x_1105_ == 0)
{
if (v___x_1103_ == 0)
{
lean_dec_ref(v___f_1104_);
lean_dec_ref(v_items_1098_);
return v___x_1099_;
}
else
{
size_t v___x_1106_; size_t v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = ((size_t)0ULL);
v___x_1107_ = lean_usize_of_nat(v___x_1101_);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1102_, v___f_1104_, v_items_1098_, v___x_1106_, v___x_1107_, v___x_1099_);
return v___x_1108_;
}
}
else
{
size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = lean_usize_of_nat(v___x_1101_);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1102_, v___f_1104_, v_items_1098_, v___x_1109_, v___x_1110_, v___x_1099_);
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_filterMap(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_00_u03b3_1114_, lean_object* v_cmp_1115_, lean_object* v_f_1116_, lean_object* v_t_1117_){
_start:
{
lean_object* v_items_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_items_1118_ = lean_ctor_get(v_t_1117_, 0);
lean_inc_ref(v_items_1118_);
lean_dec_ref(v_t_1117_);
v___x_1119_ = lean_obj_once(&l_Lake_Toml_RBDict_empty___closed__0, &l_Lake_Toml_RBDict_empty___closed__0_once, _init_l_Lake_Toml_RBDict_empty___closed__0);
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_array_get_size(v_items_1118_);
v___x_1122_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v___x_1123_ = lean_nat_dec_lt(v___x_1120_, v___x_1121_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v_items_1118_);
lean_dec_ref(v_f_1116_);
lean_dec_ref(v_cmp_1115_);
return v___x_1119_;
}
else
{
lean_object* v___f_1124_; uint8_t v___x_1125_; 
v___f_1124_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_filterMap___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1124_, 0, v_f_1116_);
lean_closure_set(v___f_1124_, 1, v_cmp_1115_);
v___x_1125_ = lean_nat_dec_le(v___x_1121_, v___x_1121_);
if (v___x_1125_ == 0)
{
if (v___x_1123_ == 0)
{
lean_dec_ref(v___f_1124_);
lean_dec_ref(v_items_1118_);
return v___x_1119_;
}
else
{
size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = lean_usize_of_nat(v___x_1121_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1122_, v___f_1124_, v_items_1118_, v___x_1126_, v___x_1127_, v___x_1119_);
return v___x_1128_;
}
}
else
{
size_t v___x_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = lean_usize_of_nat(v___x_1121_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1122_, v___f_1124_, v_items_1118_, v___x_1129_, v___x_1130_, v___x_1119_);
return v___x_1131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg___lam__0(lean_object* v_f_1132_, lean_object* v_s_1133_, lean_object* v_x_1134_){
_start:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1137_; 
v_fst_1135_ = lean_ctor_get(v_x_1134_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v_x_1134_, 1);
lean_inc(v_snd_1136_);
lean_dec_ref(v_x_1134_);
v___x_1137_ = lean_apply_3(v_f_1132_, v_s_1133_, v_fst_1135_, v_snd_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___redArg(lean_object* v_inst_1138_, lean_object* v_f_1139_, lean_object* v_init_1140_, lean_object* v_t_1141_){
_start:
{
lean_object* v_toApplicative_1142_; lean_object* v_items_1143_; lean_object* v_toPure_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_toApplicative_1142_ = lean_ctor_get(v_inst_1138_, 0);
v_items_1143_ = lean_ctor_get(v_t_1141_, 0);
lean_inc_ref(v_items_1143_);
lean_dec_ref(v_t_1141_);
v_toPure_1144_ = lean_ctor_get(v_toApplicative_1142_, 1);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = lean_array_get_size(v_items_1143_);
v___x_1147_ = lean_nat_dec_lt(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_inc(v_toPure_1144_);
lean_dec_ref(v_items_1143_);
lean_dec(v_f_1139_);
lean_dec_ref(v_inst_1138_);
v___x_1148_ = lean_apply_2(v_toPure_1144_, lean_box(0), v_init_1140_);
return v___x_1148_;
}
else
{
lean_object* v___f_1149_; uint8_t v___x_1150_; 
v___f_1149_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1149_, 0, v_f_1139_);
v___x_1150_ = lean_nat_dec_le(v___x_1146_, v___x_1146_);
if (v___x_1150_ == 0)
{
if (v___x_1147_ == 0)
{
lean_object* v___x_1151_; 
lean_inc(v_toPure_1144_);
lean_dec_ref(v___f_1149_);
lean_dec_ref(v_items_1143_);
lean_dec_ref(v_inst_1138_);
v___x_1151_ = lean_apply_2(v_toPure_1144_, lean_box(0), v_init_1140_);
return v___x_1151_;
}
else
{
size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = lean_usize_of_nat(v___x_1146_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1138_, v___f_1149_, v_items_1143_, v___x_1152_, v___x_1153_, v_init_1140_);
return v___x_1154_;
}
}
else
{
size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = lean_usize_of_nat(v___x_1146_);
v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1138_, v___f_1149_, v_items_1143_, v___x_1155_, v___x_1156_, v_init_1140_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM(lean_object* v_m_1158_, lean_object* v_00_u03c3_1159_, lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_cmp_1162_, lean_object* v_inst_1163_, lean_object* v_f_1164_, lean_object* v_init_1165_, lean_object* v_t_1166_){
_start:
{
lean_object* v_toApplicative_1167_; lean_object* v_items_1168_; lean_object* v_toPure_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_toApplicative_1167_ = lean_ctor_get(v_inst_1163_, 0);
v_items_1168_ = lean_ctor_get(v_t_1166_, 0);
lean_inc_ref(v_items_1168_);
lean_dec_ref(v_t_1166_);
v_toPure_1169_ = lean_ctor_get(v_toApplicative_1167_, 1);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_array_get_size(v_items_1168_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_inc(v_toPure_1169_);
lean_dec_ref(v_items_1168_);
lean_dec(v_f_1164_);
lean_dec_ref(v_inst_1163_);
v___x_1173_ = lean_apply_2(v_toPure_1169_, lean_box(0), v_init_1165_);
return v___x_1173_;
}
else
{
lean_object* v___f_1174_; uint8_t v___x_1175_; 
v___f_1174_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1174_, 0, v_f_1164_);
v___x_1175_ = lean_nat_dec_le(v___x_1171_, v___x_1171_);
if (v___x_1175_ == 0)
{
if (v___x_1172_ == 0)
{
lean_object* v___x_1176_; 
lean_inc(v_toPure_1169_);
lean_dec_ref(v___f_1174_);
lean_dec_ref(v_items_1168_);
lean_dec_ref(v_inst_1163_);
v___x_1176_ = lean_apply_2(v_toPure_1169_, lean_box(0), v_init_1165_);
return v___x_1176_;
}
else
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = lean_usize_of_nat(v___x_1171_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1163_, v___f_1174_, v_items_1168_, v___x_1177_, v___x_1178_, v_init_1165_);
return v___x_1179_;
}
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1171_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1163_, v___f_1174_, v_items_1168_, v___x_1180_, v___x_1181_, v_init_1165_);
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_foldM___boxed(lean_object* v_m_1183_, lean_object* v_00_u03c3_1184_, lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_cmp_1187_, lean_object* v_inst_1188_, lean_object* v_f_1189_, lean_object* v_init_1190_, lean_object* v_t_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lake_Toml_RBDict_foldM(v_m_1183_, v_00_u03c3_1184_, v_00_u03b1_1185_, v_00_u03b2_1186_, v_cmp_1187_, v_inst_1188_, v_f_1189_, v_init_1190_, v_t_1191_);
lean_dec_ref(v_cmp_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___redArg(lean_object* v_f_1193_, lean_object* v_init_1194_, lean_object* v_t_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v_items_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1196_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_items_1197_ = lean_ctor_get(v_t_1195_, 0);
lean_inc_ref(v_items_1197_);
lean_dec_ref(v_t_1195_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get_size(v_items_1197_);
v___x_1200_ = lean_nat_dec_lt(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec_ref(v_items_1197_);
lean_dec(v_f_1193_);
return v_init_1194_;
}
else
{
lean_object* v___f_1201_; size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___f_1201_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1201_, 0, v_f_1193_);
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = lean_usize_of_nat(v___x_1199_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1196_, v___f_1201_, v_items_1197_, v___x_1202_, v___x_1203_, v_init_1194_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold(lean_object* v_00_u03c3_1205_, lean_object* v_00_u03b1_1206_, lean_object* v_00_u03b2_1207_, lean_object* v_cmp_1208_, lean_object* v_f_1209_, lean_object* v_init_1210_, lean_object* v_t_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v_items_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1212_ = ((lean_object*)(l_Lake_Toml_RBDict_map___redArg___closed__9));
v_items_1213_ = lean_ctor_get(v_t_1211_, 0);
lean_inc_ref(v_items_1213_);
lean_dec_ref(v_t_1211_);
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_array_get_size(v_items_1213_);
v___x_1216_ = lean_nat_dec_lt(v___x_1214_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec_ref(v_items_1213_);
lean_dec(v_f_1209_);
return v_init_1210_;
}
else
{
lean_object* v___f_1217_; size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_1220_; 
v___f_1217_ = lean_alloc_closure((void*)(l_Lake_Toml_RBDict_foldM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1217_, 0, v_f_1209_);
v___x_1218_ = ((size_t)0ULL);
v___x_1219_ = lean_usize_of_nat(v___x_1215_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1212_, v___f_1217_, v_items_1213_, v___x_1218_, v___x_1219_, v_init_1210_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_fold___boxed(lean_object* v_00_u03c3_1221_, lean_object* v_00_u03b1_1222_, lean_object* v_00_u03b2_1223_, lean_object* v_cmp_1224_, lean_object* v_f_1225_, lean_object* v_init_1226_, lean_object* v_t_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lake_Toml_RBDict_fold(v_00_u03c3_1221_, v_00_u03b1_1222_, v_00_u03b2_1223_, v_cmp_1224_, v_f_1225_, v_init_1226_, v_t_1227_);
lean_dec_ref(v_cmp_1224_);
return v_res_1228_;
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
