// Lean compiler output
// Module: Lean.Data.NameMap.Basic
// Imports: public import Std.Data.HashSet.Basic public import Std.Data.TreeSet.Basic public import Lean.Data.SSet public import Lean.Data.Name
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_noption_none();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameMap_instRepr___aux__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__0_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__1 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__1_value;
static const lean_string_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeMap.ofList "};
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__2 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__2_value;
static const lean_ctor_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__2_value)}};
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__3 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__3_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__4 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__4_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__5 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__5_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__6 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__6_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__7 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__7_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__8 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__8_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__9 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__9_value;
static const lean_closure_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__10 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__10_value;
static const lean_ctor_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__4_value),((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__5_value)}};
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__11 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__11_value;
static const lean_ctor_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__11_value),((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__6_value),((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__7_value),((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__8_value),((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__9_value)}};
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__12 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__12_value;
static const lean_ctor_object l_Lean_NameMap_instRepr___aux__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__12_value),((lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__10_value)}};
static const lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___closed__13 = (const lean_object*)&l_Lean_NameMap_instRepr___aux__1___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameMap_instInsertProdName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameMap_instInsertProdName___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instInsertProdName___closed__0 = (const lean_object*)&l_Lean_NameMap_instInsertProdName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameSet_instInhabited;
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instInsertName___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instInsertName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instInsertName___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instInsertName___closed__0 = (const lean_object*)&l_Lean_NameSet_instInsertName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instInsertName = (const lean_object*)&l_Lean_NameSet_instInsertName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_append, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instAppend___closed__0 = (const lean_object*)&l_Lean_NameSet_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instAppend = (const lean_object*)&l_Lean_NameSet_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instSingletonName___lam__0(lean_object*);
static const lean_closure_object l_Lean_NameSet_instSingletonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instSingletonName___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instSingletonName___closed__0 = (const lean_object*)&l_Lean_NameSet_instSingletonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instSingletonName = (const lean_object*)&l_Lean_NameSet_instSingletonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instUnion = (const lean_object*)&l_Lean_NameSet_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instInter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instInter___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instInter___closed__0 = (const lean_object*)&l_Lean_NameSet_instInter___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instInter = (const lean_object*)&l_Lean_NameSet_instInter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instSDiff___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instSDiff___lam__1___closed__0 = (const lean_object*)&l_Lean_NameSet_instSDiff___lam__1___closed__0_value;
static const lean_closure_object l_Lean_NameSet_instSDiff___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instSDiff___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_NameSet_instSDiff___lam__1___closed__0_value)} };
static const lean_object* l_Lean_NameSet_instSDiff___lam__1___closed__1 = (const lean_object*)&l_Lean_NameSet_instSDiff___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameSet_instSDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_instSDiff___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSet_instSDiff___closed__0 = (const lean_object*)&l_Lean_NameSet_instSDiff___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_NameSet_instSDiff = (const lean_object*)&l_Lean_NameSet_instSDiff___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray___boxed(lean_object*);
static const lean_closure_object l_Lean_NameSSet_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSSet_empty___closed__0 = (const lean_object*)&l_Lean_NameSSet_empty___closed__0_value;
static const lean_closure_object l_Lean_NameSSet_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSSet_empty___closed__1 = (const lean_object*)&l_Lean_NameSSet_empty___closed__1_value;
static lean_once_cell_t l_Lean_NameSSet_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameSSet_empty___closed__2;
LEAN_EXPORT lean_object* l_Lean_NameSSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameSSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameSSet_instInhabited;
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_NameHashSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameHashSet_empty___closed__0;
static lean_once_cell_t l_Lean_NameHashSet_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameHashSet_empty___closed__1;
static lean_once_cell_t l_Lean_NameHashSet_empty___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameHashSet_empty___closed__2;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instInhabited;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(1);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___lam__0(lean_object* v_x1_3_, lean_object* v_x2_4_, lean_object* v_x3_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v_x1_3_);
lean_ctor_set(v___x_6_, 1, v_x2_4_);
v___x_7_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v_x3_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg(lean_object* v_inst_32_, lean_object* v_m_33_, lean_object* v_prec_34_){
_start:
{
lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___f_35_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__0));
v___x_36_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__1));
v___x_37_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__3));
v___f_38_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_38_, 0, v_inst_32_);
v___x_39_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_39_, 0, lean_box(0));
lean_closure_set(v___x_39_, 1, lean_box(0));
lean_closure_set(v___x_39_, 2, v___x_36_);
lean_closure_set(v___x_39_, 3, v___f_38_);
v___x_40_ = lean_box(0);
v___x_41_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__13));
v___x_42_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_41_, v___f_35_, v___x_40_, v_m_33_);
v___x_43_ = l_List_repr___redArg(v___x_39_, v___x_42_);
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_37_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = l_Repr_addAppParen(v___x_44_, v_prec_34_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___boxed(lean_object* v_inst_46_, lean_object* v_m_47_, lean_object* v_prec_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_NameMap_instRepr___aux__1___redArg(v_inst_46_, v_m_47_, v_prec_48_);
lean_dec(v_prec_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_m_52_, lean_object* v_prec_53_){
_start:
{
lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___f_54_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__0));
v___x_55_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__1));
v___x_56_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__3));
v___f_57_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_57_, 0, v_inst_51_);
v___x_58_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_58_, 0, lean_box(0));
lean_closure_set(v___x_58_, 1, lean_box(0));
lean_closure_set(v___x_58_, 2, v___x_55_);
lean_closure_set(v___x_58_, 3, v___f_57_);
v___x_59_ = lean_box(0);
v___x_60_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__13));
v___x_61_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_60_, v___f_54_, v___x_59_, v_m_52_);
v___x_62_ = l_List_repr___redArg(v___x_58_, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_56_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = l_Repr_addAppParen(v___x_63_, v_prec_53_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___boxed(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, lean_object* v_m_67_, lean_object* v_prec_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_NameMap_instRepr___aux__1(v_00_u03b1_65_, v_inst_66_, v_m_67_, v_prec_68_);
lean_dec(v_prec_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_alloc_closure((void*)(l_Lean_NameMap_instRepr___aux__1___boxed), 4, 2);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, v_inst_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object* v_00_u03b1_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_closure((void*)(l_Lean_NameMap_instRepr___aux__1___boxed), 4, 2);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, v_inst_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object* v_00_u03b1_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(1);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object* v_00_u03b1_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(1);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object* v_k_79_, lean_object* v_v_80_, lean_object* v_t_81_){
_start:
{
if (lean_obj_tag(v_t_81_) == 0)
{
lean_object* v_size_82_; lean_object* v_k_83_; lean_object* v_v_84_; lean_object* v_l_85_; lean_object* v_r_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_366_; 
v_size_82_ = lean_ctor_get(v_t_81_, 0);
v_k_83_ = lean_ctor_get(v_t_81_, 1);
v_v_84_ = lean_ctor_get(v_t_81_, 2);
v_l_85_ = lean_ctor_get(v_t_81_, 3);
v_r_86_ = lean_ctor_get(v_t_81_, 4);
v_isSharedCheck_366_ = !lean_is_exclusive(v_t_81_);
if (v_isSharedCheck_366_ == 0)
{
v___x_88_ = v_t_81_;
v_isShared_89_ = v_isSharedCheck_366_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_r_86_);
lean_inc(v_l_85_);
lean_inc(v_v_84_);
lean_inc(v_k_83_);
lean_inc(v_size_82_);
lean_dec(v_t_81_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_366_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
uint8_t v___x_90_; 
v___x_90_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_79_, v_k_83_);
switch(v___x_90_)
{
case 0:
{
lean_object* v_impl_91_; lean_object* v___x_92_; 
lean_dec(v_size_82_);
v_impl_91_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_79_, v_v_80_, v_l_85_);
v___x_92_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_86_) == 0)
{
lean_object* v_size_93_; lean_object* v_size_94_; lean_object* v_k_95_; lean_object* v_v_96_; lean_object* v_l_97_; lean_object* v_r_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_size_93_ = lean_ctor_get(v_r_86_, 0);
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
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 3, v_impl_91_);
lean_ctor_set(v___x_88_, 0, v___x_103_);
v___x_105_ = v___x_88_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_impl_91_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_r_86_);
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
v___x_128_ = lean_nat_add(v___y_125_, v___y_127_);
lean_dec(v___y_127_);
lean_dec(v___y_125_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 4, v_r_86_);
lean_ctor_set(v___x_120_, 3, v_r_115_);
lean_ctor_set(v___x_120_, 2, v_v_84_);
lean_ctor_set(v___x_120_, 1, v_k_83_);
lean_ctor_set(v___x_120_, 0, v___x_128_);
v___x_130_ = v___x_120_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_r_115_);
lean_ctor_set(v_reuseFailAlloc_134_, 4, v_r_86_);
v___x_130_ = v_reuseFailAlloc_134_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 4, v___x_130_);
lean_ctor_set(v___x_108_, 3, v___y_126_);
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
lean_ctor_set(v_reuseFailAlloc_133_, 3, v___y_126_);
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
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_l_114_);
lean_ctor_set(v___x_88_, 3, v_l_97_);
lean_ctor_set(v___x_88_, 2, v_v_96_);
lean_ctor_set(v___x_88_, 1, v_k_95_);
lean_ctor_set(v___x_88_, 0, v___x_138_);
v___x_140_ = v___x_88_;
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
v___y_125_ = v___x_141_;
v___y_126_ = v___x_140_;
v___y_127_ = v_size_142_;
goto v___jp_124_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___y_125_ = v___x_141_;
v___y_126_ = v___x_140_;
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
lean_del_object(v___x_88_);
v___x_153_ = lean_nat_add(v___x_92_, v_size_94_);
lean_dec(v_size_94_);
v___x_154_ = lean_nat_add(v___x_153_, v_size_93_);
lean_dec(v___x_153_);
v___x_155_ = lean_nat_add(v___x_92_, v_size_93_);
v___x_156_ = lean_nat_add(v___x_155_, v_size_111_);
lean_dec(v___x_155_);
lean_inc_ref(v_r_86_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 4, v_r_86_);
lean_ctor_set(v___x_108_, 3, v_r_98_);
lean_ctor_set(v___x_108_, 2, v_v_84_);
lean_ctor_set(v___x_108_, 1, v_k_83_);
lean_ctor_set(v___x_108_, 0, v___x_156_);
v___x_158_ = v___x_108_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_171_, 3, v_r_98_);
lean_ctor_set(v_reuseFailAlloc_171_, 4, v_r_86_);
v___x_158_ = v_reuseFailAlloc_171_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_isSharedCheck_165_ = !lean_is_exclusive(v_r_86_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; lean_object* v_unused_167_; lean_object* v_unused_168_; lean_object* v_unused_169_; lean_object* v_unused_170_; 
v_unused_166_ = lean_ctor_get(v_r_86_, 4);
lean_dec(v_unused_166_);
v_unused_167_ = lean_ctor_get(v_r_86_, 3);
lean_dec(v_unused_167_);
v_unused_168_ = lean_ctor_get(v_r_86_, 2);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_r_86_, 1);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_r_86_, 0);
lean_dec(v_unused_170_);
v___x_160_ = v_r_86_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_dec(v_r_86_);
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
lean_ctor_set(v___x_183_, 2, v_v_84_);
lean_ctor_set(v___x_183_, 1, v_k_83_);
lean_ctor_set(v___x_183_, 0, v___x_92_);
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_191_, 3, v_r_179_);
lean_ctor_set(v_reuseFailAlloc_191_, 4, v_r_179_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_187_);
lean_ctor_set(v___x_88_, 3, v_l_178_);
lean_ctor_set(v___x_88_, 2, v_v_181_);
lean_ctor_set(v___x_88_, 1, v_k_180_);
lean_ctor_set(v___x_88_, 0, v___x_185_);
v___x_189_ = v___x_88_;
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
lean_ctor_set(v___x_199_, 2, v_v_84_);
lean_ctor_set(v___x_199_, 1, v_k_83_);
lean_ctor_set(v___x_199_, 0, v___x_92_);
v___x_210_ = v___x_199_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_214_, 3, v_l_178_);
lean_ctor_set(v_reuseFailAlloc_214_, 4, v_l_178_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_210_);
lean_ctor_set(v___x_88_, 3, v___x_208_);
lean_ctor_set(v___x_88_, 2, v_v_202_);
lean_ctor_set(v___x_88_, 1, v_k_201_);
lean_ctor_set(v___x_88_, 0, v___x_206_);
v___x_212_ = v___x_88_;
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
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_r_195_);
lean_ctor_set(v___x_88_, 3, v_impl_91_);
lean_ctor_set(v___x_88_, 0, v___x_224_);
v___x_226_ = v___x_88_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_v_84_);
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
lean_dec(v_v_84_);
lean_dec(v_k_83_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v_v_80_);
lean_ctor_set(v___x_88_, 1, v_k_79_);
v___x_229_ = v___x_88_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_size_82_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_k_79_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_v_80_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_l_85_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_r_86_);
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
lean_dec(v_size_82_);
v_impl_231_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_79_, v_v_80_, v_r_86_);
v___x_232_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_85_) == 0)
{
lean_object* v_size_233_; lean_object* v_size_234_; lean_object* v_k_235_; lean_object* v_v_236_; lean_object* v_l_237_; lean_object* v_r_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_size_233_ = lean_ctor_get(v_l_85_, 0);
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
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_impl_231_);
lean_ctor_set(v___x_88_, 0, v___x_243_);
v___x_245_ = v___x_88_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_l_85_);
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
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_l_253_);
lean_ctor_set(v___x_88_, 0, v___x_277_);
v___x_279_ = v___x_88_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_l_85_);
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
lean_del_object(v___x_88_);
v___x_292_ = lean_nat_add(v___x_232_, v_size_233_);
v___x_293_ = lean_nat_add(v___x_292_, v_size_234_);
lean_dec(v_size_234_);
v___x_294_ = lean_nat_add(v___x_292_, v_size_250_);
lean_dec(v___x_292_);
lean_inc_ref(v_l_85_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 4, v_l_237_);
lean_ctor_set(v___x_248_, 3, v_l_85_);
lean_ctor_set(v___x_248_, 2, v_v_84_);
lean_ctor_set(v___x_248_, 1, v_k_83_);
lean_ctor_set(v___x_248_, 0, v___x_294_);
v___x_296_ = v___x_248_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_l_85_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_l_237_);
v___x_296_ = v_reuseFailAlloc_309_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_isSharedCheck_303_ = !lean_is_exclusive(v_l_85_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; lean_object* v_unused_305_; lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; 
v_unused_304_ = lean_ctor_get(v_l_85_, 4);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_l_85_, 3);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_l_85_, 2);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_l_85_, 1);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_l_85_, 0);
lean_dec(v_unused_308_);
v___x_298_ = v_l_85_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_l_85_);
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
lean_ctor_set(v___x_326_, 2, v_v_84_);
lean_ctor_set(v___x_326_, 1, v_k_83_);
lean_ctor_set(v___x_326_, 0, v___x_232_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_v_84_);
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
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_332_);
lean_ctor_set(v___x_88_, 3, v___x_330_);
lean_ctor_set(v___x_88_, 2, v_v_324_);
lean_ctor_set(v___x_88_, 1, v_k_323_);
lean_ctor_set(v___x_88_, 0, v___x_328_);
v___x_334_ = v___x_88_;
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
lean_ctor_set(v___x_349_, 2, v_v_84_);
lean_ctor_set(v___x_349_, 1, v_k_83_);
lean_ctor_set(v___x_349_, 0, v___x_232_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_v_84_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_l_316_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_l_316_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_r_345_);
lean_ctor_set(v___x_88_, 3, v___x_353_);
lean_ctor_set(v___x_88_, 2, v_v_347_);
lean_ctor_set(v___x_88_, 1, v_k_346_);
lean_ctor_set(v___x_88_, 0, v___x_351_);
v___x_355_ = v___x_88_;
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
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v_impl_231_);
lean_ctor_set(v___x_88_, 3, v_r_345_);
lean_ctor_set(v___x_88_, 0, v___x_362_);
v___x_364_ = v___x_88_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_83_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_v_84_);
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
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_k_79_);
lean_ctor_set(v___x_368_, 2, v_v_80_);
lean_ctor_set(v___x_368_, 3, v_t_81_);
lean_ctor_set(v___x_368_, 4, v_t_81_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object* v_m_369_, lean_object* v_n_370_, lean_object* v_a_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_370_, v_a_371_, v_m_369_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object* v_00_u03b1_373_, lean_object* v_m_374_, lean_object* v_n_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_375_, v_a_376_, v_m_374_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0(lean_object* v_00_u03b2_378_, lean_object* v_k_379_, lean_object* v_v_380_, lean_object* v_t_381_, lean_object* v_hl_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_379_, v_v_380_, v_t_381_);
return v___x_383_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object* v_k_384_, lean_object* v_t_385_){
_start:
{
if (lean_obj_tag(v_t_385_) == 0)
{
lean_object* v_k_386_; lean_object* v_l_387_; lean_object* v_r_388_; uint8_t v___x_389_; 
v_k_386_ = lean_ctor_get(v_t_385_, 1);
v_l_387_ = lean_ctor_get(v_t_385_, 3);
v_r_388_ = lean_ctor_get(v_t_385_, 4);
v___x_389_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_384_, v_k_386_);
switch(v___x_389_)
{
case 0:
{
v_t_385_ = v_l_387_;
goto _start;
}
case 1:
{
uint8_t v___x_391_; 
v___x_391_ = 1;
return v___x_391_;
}
default: 
{
v_t_385_ = v_r_388_;
goto _start;
}
}
}
else
{
uint8_t v___x_393_; 
v___x_393_ = 0;
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg___boxed(lean_object* v_k_394_, lean_object* v_t_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_394_, v_t_395_);
lean_dec(v_t_395_);
lean_dec(v_k_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains___redArg(lean_object* v_m_398_, lean_object* v_n_399_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_399_, v_m_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object* v_m_401_, lean_object* v_n_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Lean_NameMap_contains___redArg(v_m_401_, v_n_402_);
lean_dec(v_n_402_);
lean_dec(v_m_401_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains(lean_object* v_00_u03b1_405_, lean_object* v_m_406_, lean_object* v_n_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_407_, v_m_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object* v_00_u03b1_409_, lean_object* v_m_410_, lean_object* v_n_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lean_NameMap_contains(v_00_u03b1_409_, v_m_410_, v_n_411_);
lean_dec(v_n_411_);
lean_dec(v_m_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(lean_object* v_00_u03b2_414_, lean_object* v_k_415_, lean_object* v_t_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_415_, v_t_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___boxed(lean_object* v_00_u03b2_418_, lean_object* v_k_419_, lean_object* v_t_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(v_00_u03b2_418_, v_k_419_, v_t_420_);
lean_dec(v_t_420_);
lean_dec(v_k_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object* v_t_423_, lean_object* v_k_424_){
_start:
{
if (lean_obj_tag(v_t_423_) == 0)
{
lean_object* v_k_425_; lean_object* v_v_426_; lean_object* v_l_427_; lean_object* v_r_428_; uint8_t v___x_429_; 
v_k_425_ = lean_ctor_get(v_t_423_, 1);
v_v_426_ = lean_ctor_get(v_t_423_, 2);
v_l_427_ = lean_ctor_get(v_t_423_, 3);
v_r_428_ = lean_ctor_get(v_t_423_, 4);
v___x_429_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_424_, v_k_425_);
switch(v___x_429_)
{
case 0:
{
v_t_423_ = v_l_427_;
goto _start;
}
case 1:
{
lean_object* v___x_431_; 
lean_inc(v_v_426_);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_v_426_);
return v___x_431_;
}
default: 
{
v_t_423_ = v_r_428_;
goto _start;
}
}
}
else
{
lean_object* v___x_433_; 
v___x_433_ = lean_box(0);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg___boxed(lean_object* v_t_434_, lean_object* v_k_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_434_, v_k_435_);
lean_dec(v_k_435_);
lean_dec(v_t_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object* v_m_437_, lean_object* v_n_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_437_, v_n_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object* v_m_440_, lean_object* v_n_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_NameMap_find_x3f___redArg(v_m_440_, v_n_441_);
lean_dec(v_n_441_);
lean_dec(v_m_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object* v_00_u03b1_443_, lean_object* v_m_444_, lean_object* v_n_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_444_, v_n_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object* v_00_u03b1_447_, lean_object* v_m_448_, lean_object* v_n_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_NameMap_find_x3f(v_00_u03b1_447_, v_m_448_, v_n_449_);
lean_dec(v_n_449_);
lean_dec(v_m_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(lean_object* v_00_u03b4_451_, lean_object* v_t_452_, lean_object* v_k_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_452_, v_k_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b4_455_, lean_object* v_t_456_, lean_object* v_k_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(v_00_u03b4_455_, v_t_456_, v_k_457_);
lean_dec(v_k_457_);
lean_dec(v_t_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___lam__0(lean_object* v_e_459_, lean_object* v_s_460_){
_start:
{
lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_463_; 
v_fst_461_ = lean_ctor_get(v_e_459_, 0);
lean_inc(v_fst_461_);
v_snd_462_ = lean_ctor_get(v_e_459_, 1);
lean_inc(v_snd_462_);
lean_dec_ref(v_e_459_);
v___x_463_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_461_, v_snd_462_, v_s_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName(lean_object* v_00_u03b1_465_){
_start:
{
lean_object* v___f_466_; 
v___f_466_ = ((lean_object*)(l_Lean_NameMap_instInsertProdName___closed__0));
return v___f_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_467_, lean_object* v_a_468_, lean_object* v_b_469_, lean_object* v_c_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_a_468_);
lean_ctor_set(v___x_471_, 1, v_b_469_);
v___x_472_ = lean_apply_2(v_f_467_, v___x_471_, v_c_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_473_, lean_object* v_____do__lift_474_){
_start:
{
lean_object* v_a_475_; lean_object* v___x_476_; 
v_a_475_ = lean_ctor_get(v_____do__lift_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref(v_____do__lift_474_);
v___x_476_ = lean_apply_2(v_toPure_473_, lean_box(0), v_a_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg(lean_object* v_inst_477_, lean_object* v_m_478_, lean_object* v_init_479_, lean_object* v_f_480_){
_start:
{
lean_object* v_toApplicative_481_; lean_object* v_toBind_482_; lean_object* v_toPure_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v___x_487_; 
v_toApplicative_481_ = lean_ctor_get(v_inst_477_, 0);
v_toBind_482_ = lean_ctor_get(v_inst_477_, 1);
lean_inc(v_toBind_482_);
v_toPure_483_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc(v_toPure_483_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_484_, 0, v_f_480_);
v___x_485_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_477_, v___f_484_, v_init_479_, v_m_478_);
v___f_486_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_486_, 0, v_toPure_483_);
v___x_487_ = lean_apply_4(v_toBind_482_, lean_box(0), lean_box(0), v___x_485_, v___f_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1(lean_object* v_00_u03b1_488_, lean_object* v_m_489_, lean_object* v_inst_490_, lean_object* v_00_u03b2_491_, lean_object* v_m_492_, lean_object* v_init_493_, lean_object* v_f_494_){
_start:
{
lean_object* v_toApplicative_495_; lean_object* v_toBind_496_; lean_object* v_toPure_497_; lean_object* v___f_498_; lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_501_; 
v_toApplicative_495_ = lean_ctor_get(v_inst_490_, 0);
v_toBind_496_ = lean_ctor_get(v_inst_490_, 1);
lean_inc(v_toBind_496_);
v_toPure_497_ = lean_ctor_get(v_toApplicative_495_, 1);
lean_inc(v_toPure_497_);
v___f_498_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_498_, 0, v_f_494_);
v___x_499_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_490_, v___f_498_, v_init_493_, v_m_492_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_500_, 0, v_toPure_497_);
v___x_501_ = lean_apply_4(v_toBind_496_, lean_box(0), lean_box(0), v___x_499_, v___f_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___redArg(lean_object* v_inst_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_503_, 0, lean_box(0));
lean_closure_set(v___x_503_, 1, lean_box(0));
lean_closure_set(v___x_503_, 2, v_inst_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad(lean_object* v_00_u03b1_504_, lean_object* v_m_505_, lean_object* v_inst_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_507_, 0, lean_box(0));
lean_closure_set(v___x_507_, 1, lean_box(0));
lean_closure_set(v___x_507_, 2, v_inst_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object* v_f_508_, lean_object* v_t_509_){
_start:
{
if (lean_obj_tag(v_t_509_) == 0)
{
lean_object* v_k_510_; lean_object* v_v_511_; lean_object* v_l_512_; lean_object* v_r_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_k_510_ = lean_ctor_get(v_t_509_, 1);
lean_inc_n(v_k_510_, 2);
v_v_511_ = lean_ctor_get(v_t_509_, 2);
lean_inc_n(v_v_511_, 2);
v_l_512_ = lean_ctor_get(v_t_509_, 3);
lean_inc(v_l_512_);
v_r_513_ = lean_ctor_get(v_t_509_, 4);
lean_inc(v_r_513_);
lean_dec_ref_known(v_t_509_, 5);
lean_inc_ref(v_f_508_);
v___x_514_ = lean_apply_2(v_f_508_, v_k_510_, v_v_511_);
v___x_515_ = lean_unbox(v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v_impl_516_; lean_object* v_impl_517_; lean_object* v___x_518_; 
lean_dec(v_v_511_);
lean_dec(v_k_510_);
lean_inc_ref(v_f_508_);
v_impl_516_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_508_, v_l_512_);
v_impl_517_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_508_, v_r_513_);
v___x_518_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_516_, v_impl_517_);
return v___x_518_;
}
else
{
lean_object* v_impl_519_; lean_object* v_impl_520_; lean_object* v___x_521_; 
lean_inc_ref(v_f_508_);
v_impl_519_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_508_, v_l_512_);
v_impl_520_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_508_, v_r_513_);
v___x_521_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_510_, v_v_511_, v_impl_519_, v_impl_520_);
return v___x_521_;
}
}
else
{
lean_dec_ref(v_f_508_);
return v_t_509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object* v_f_522_, lean_object* v_m_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_522_, v_m_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object* v_00_u03b1_525_, lean_object* v_f_526_, lean_object* v_m_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_526_, v_m_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(lean_object* v_00_u03b1_529_, lean_object* v_f_530_, lean_object* v_t_531_, lean_object* v_hl_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_530_, v_t_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_NameSet_empty(void){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = lean_box(1);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_NameSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_box(1);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_NameSet_instInhabited(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_box(1);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object* v_s_537_, lean_object* v_n_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_538_, v_s_537_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_box(0);
v___x_541_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_538_, v___x_540_, v_s_537_);
return v___x_541_;
}
else
{
lean_dec(v_n_538_);
return v_s_537_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object* v_s_542_, lean_object* v_n_543_){
_start:
{
uint8_t v___x_544_; 
v___x_544_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_543_, v_s_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object* v_s_545_, lean_object* v_n_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l_Lean_NameSet_contains(v_s_545_, v_n_546_);
lean_dec(v_n_546_);
lean_dec(v_s_545_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInsertName___lam__0(lean_object* v_n_549_, lean_object* v_s_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_NameSet_insert(v_s_550_, v_n_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_554_, lean_object* v_a_555_, lean_object* v_b_556_, lean_object* v_c_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_apply_2(v_f_554_, v_a_555_, v_c_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg(lean_object* v_inst_559_, lean_object* v_m_560_, lean_object* v_init_561_, lean_object* v_f_562_){
_start:
{
lean_object* v_toApplicative_563_; lean_object* v_toBind_564_; lean_object* v_toPure_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v___x_569_; 
v_toApplicative_563_ = lean_ctor_get(v_inst_559_, 0);
v_toBind_564_ = lean_ctor_get(v_inst_559_, 1);
lean_inc(v_toBind_564_);
v_toPure_565_ = lean_ctor_get(v_toApplicative_563_, 1);
lean_inc(v_toPure_565_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_566_, 0, v_f_562_);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_559_, v___f_566_, v_init_561_, v_m_560_);
v___f_568_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_568_, 0, v_toPure_565_);
v___x_569_ = lean_apply_4(v_toBind_564_, lean_box(0), lean_box(0), v___x_567_, v___f_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1(lean_object* v_m_570_, lean_object* v_inst_571_, lean_object* v_00_u03b2_572_, lean_object* v_m_573_, lean_object* v_init_574_, lean_object* v_f_575_){
_start:
{
lean_object* v_toApplicative_576_; lean_object* v_toBind_577_; lean_object* v_toPure_578_; lean_object* v___f_579_; lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___x_582_; 
v_toApplicative_576_ = lean_ctor_get(v_inst_571_, 0);
v_toBind_577_ = lean_ctor_get(v_inst_571_, 1);
lean_inc(v_toBind_577_);
v_toPure_578_ = lean_ctor_get(v_toApplicative_576_, 1);
lean_inc(v_toPure_578_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_579_, 0, v_f_575_);
v___x_580_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_571_, v___f_579_, v_init_574_, v_m_573_);
v___f_581_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_581_, 0, v_toPure_578_);
v___x_582_ = lean_apply_4(v_toBind_577_, lean_box(0), lean_box(0), v___x_580_, v___f_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___redArg(lean_object* v_inst_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_584_, 0, lean_box(0));
lean_closure_set(v___x_584_, 1, v_inst_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad(lean_object* v_m_585_, lean_object* v_inst_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_587_, 0, lean_box(0));
lean_closure_set(v___x_587_, 1, v_inst_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_b_u2082_590_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0));
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_594_, lean_object* v_x_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_594_, v_x_595_);
lean_dec(v_x_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(lean_object* v_b_u2082_597_, lean_object* v_k_598_, lean_object* v_t_599_){
_start:
{
if (lean_obj_tag(v_t_599_) == 0)
{
lean_object* v_size_600_; lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v_l_603_; lean_object* v_r_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_619_; 
v_size_600_ = lean_ctor_get(v_t_599_, 0);
v_k_601_ = lean_ctor_get(v_t_599_, 1);
v_v_602_ = lean_ctor_get(v_t_599_, 2);
v_l_603_ = lean_ctor_get(v_t_599_, 3);
v_r_604_ = lean_ctor_get(v_t_599_, 4);
v_isSharedCheck_619_ = !lean_is_exclusive(v_t_599_);
if (v_isSharedCheck_619_ == 0)
{
v___x_606_ = v_t_599_;
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_r_604_);
lean_inc(v_l_603_);
lean_inc(v_v_602_);
lean_inc(v_k_601_);
lean_inc(v_size_600_);
lean_dec(v_t_599_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_619_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
uint8_t v___x_608_; 
v___x_608_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_598_, v_k_601_);
switch(v___x_608_)
{
case 0:
{
lean_object* v_impl_609_; lean_object* v___x_610_; 
lean_del_object(v___x_606_);
lean_dec(v_size_600_);
v_impl_609_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_597_, v_k_598_, v_l_603_);
v___x_610_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_601_, v_v_602_, v_impl_609_, v_r_604_);
return v___x_610_;
}
case 1:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_val_613_; lean_object* v___x_615_; 
lean_dec(v_k_601_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_v_602_);
v___x_612_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_597_, v___x_611_);
lean_dec_ref_known(v___x_611_, 1);
v_val_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_val_613_);
lean_dec(v___x_612_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 2, v_val_613_);
lean_ctor_set(v___x_606_, 1, v_k_598_);
v___x_615_ = v___x_606_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_size_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_val_613_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_l_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_r_604_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
default: 
{
lean_object* v_impl_617_; lean_object* v___x_618_; 
lean_del_object(v___x_606_);
lean_dec(v_size_600_);
v_impl_617_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_597_, v_k_598_, v_r_604_);
v___x_618_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_601_, v_v_602_, v_l_603_, v_impl_617_);
return v___x_618_;
}
}
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_val_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_620_ = lean_box(0);
v___x_621_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_597_, v___x_620_);
v_val_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_622_);
lean_dec(v___x_621_);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v_k_598_);
lean_ctor_set(v___x_624_, 2, v_val_622_);
lean_ctor_set(v___x_624_, 3, v_t_599_);
lean_ctor_set(v___x_624_, 4, v_t_599_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(lean_object* v_init_625_, lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_object* v_k_627_; lean_object* v_v_628_; lean_object* v_l_629_; lean_object* v_r_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_k_627_ = lean_ctor_get(v_x_626_, 1);
lean_inc(v_k_627_);
v_v_628_ = lean_ctor_get(v_x_626_, 2);
lean_inc(v_v_628_);
v_l_629_ = lean_ctor_get(v_x_626_, 3);
lean_inc(v_l_629_);
v_r_630_ = lean_ctor_get(v_x_626_, 4);
lean_inc(v_r_630_);
lean_dec_ref_known(v_x_626_, 5);
v___x_631_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_625_, v_l_629_);
v___x_632_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_v_628_, v_k_627_, v___x_631_);
v_init_625_ = v___x_632_;
v_x_626_ = v_r_630_;
goto _start;
}
else
{
return v_init_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object* v_s_634_, lean_object* v_t_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_s_634_, v_t_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(lean_object* v_b_u2082_637_, lean_object* v_k_638_, lean_object* v_t_639_, lean_object* v_hl_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_637_, v_k_638_, v_t_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(lean_object* v_init_642_, lean_object* v_t_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_642_, v_t_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSingletonName___lam__0(lean_object* v_n_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_box(1);
v___x_649_ = l_Lean_NameSet_insert(v___x_648_, v_n_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0(lean_object* v_t_653_, lean_object* v_c_654_, lean_object* v_a_655_, lean_object* v_x_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_a_655_, v_t_653_);
if (v___x_657_ == 0)
{
lean_dec(v_a_655_);
return v_c_654_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_NameSet_insert(v_c_654_, v_a_655_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0___boxed(lean_object* v_t_659_, lean_object* v_c_660_, lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_NameSet_instInter___lam__0(v_t_659_, v_c_660_, v_a_661_, v_x_662_);
lean_dec(v_t_659_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__1(lean_object* v_s_664_, lean_object* v_t_665_){
_start:
{
lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___f_666_ = lean_alloc_closure((void*)(l_Lean_NameSet_instInter___lam__0___boxed), 4, 1);
lean_closure_set(v___f_666_, 0, v_t_665_);
v___x_667_ = lean_box(1);
v___x_668_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_666_, v___x_667_, v_s_664_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__0(lean_object* v___x_671_, lean_object* v_c_672_, lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_671_, v_a_673_, v_c_672_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__1(lean_object* v_s_679_, lean_object* v_t_680_){
_start:
{
lean_object* v___f_681_; lean_object* v___x_682_; 
v___f_681_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__1));
v___x_682_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_681_, v_s_679_, v_t_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(lean_object* v_f_685_, lean_object* v_t_686_){
_start:
{
if (lean_obj_tag(v_t_686_) == 0)
{
lean_object* v_k_687_; lean_object* v_v_688_; lean_object* v_l_689_; lean_object* v_r_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_k_687_ = lean_ctor_get(v_t_686_, 1);
lean_inc_n(v_k_687_, 2);
v_v_688_ = lean_ctor_get(v_t_686_, 2);
lean_inc(v_v_688_);
v_l_689_ = lean_ctor_get(v_t_686_, 3);
lean_inc(v_l_689_);
v_r_690_ = lean_ctor_get(v_t_686_, 4);
lean_inc(v_r_690_);
lean_dec_ref_known(v_t_686_, 5);
lean_inc_ref(v_f_685_);
v___x_691_ = lean_apply_1(v_f_685_, v_k_687_);
v___x_692_ = lean_unbox(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v_impl_693_; lean_object* v_impl_694_; lean_object* v___x_695_; 
lean_dec(v_v_688_);
lean_dec(v_k_687_);
lean_inc_ref(v_f_685_);
v_impl_693_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_685_, v_l_689_);
v_impl_694_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_685_, v_r_690_);
v___x_695_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_693_, v_impl_694_);
return v___x_695_;
}
else
{
lean_object* v_impl_696_; lean_object* v_impl_697_; lean_object* v___x_698_; 
lean_inc_ref(v_f_685_);
v_impl_696_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_685_, v_l_689_);
v_impl_697_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_685_, v_r_690_);
v___x_698_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_687_, v_v_688_, v_impl_696_, v_impl_697_);
return v___x_698_;
}
}
else
{
lean_dec_ref(v_f_685_);
return v_t_686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object* v_f_699_, lean_object* v_s_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_699_, v_s_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(lean_object* v_f_702_, lean_object* v_t_703_, lean_object* v_hl_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_702_, v_t_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList(lean_object* v_l_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_708_ = l_Std_TreeSet_ofList___redArg(v_l_706_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList___boxed(lean_object* v_l_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_NameSet_ofList(v_l_709_);
lean_dec(v_l_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray(lean_object* v_l_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_713_ = l_Std_TreeSet_ofArray___redArg(v_l_711_, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray___boxed(lean_object* v_l_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_NameSet_ofArray(v_l_714_);
lean_dec_ref(v_l_714_);
return v_res_715_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__2(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_719_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_720_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v___x_719_, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty(void){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_NameSSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_722_;
}
}
static lean_object* _init_l_Lean_NameSSet_instInhabited(void){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object* v_s_724_, lean_object* v_n_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_727_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_728_ = lean_box(0);
v___x_729_ = l_Lean_SMap_insert___redArg(v___x_726_, v___x_727_, v_s_724_, v_n_725_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object* v_s_730_, lean_object* v_n_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_733_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_734_ = l_Lean_SMap_contains___redArg(v___x_732_, v___x_733_, v_s_730_, v_n_731_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object* v_s_735_, lean_object* v_n_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l_Lean_NameSSet_contains(v_s_735_, v_n_736_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__0(void){
_start:
{
lean_object* v_cellCount_739_; lean_object* v___x_740_; 
v_cellCount_739_ = lean_unsigned_to_nat(16u);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__1(void){
_start:
{
lean_object* v_cellCount_741_; lean_object* v___x_742_; 
v_cellCount_741_ = lean_unsigned_to_nat(16u);
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__2(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
v___x_744_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__0, &l_Lean_NameHashSet_empty___closed__0_once, _init_l_Lean_NameHashSet_empty___closed__0);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
lean_ctor_set(v___x_746_, 2, v___x_743_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty(void){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__2, &l_Lean_NameHashSet_empty___closed__2_once, _init_l_Lean_NameHashSet_empty___closed__2);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__2, &l_Lean_NameHashSet_empty___closed__2_once, _init_l_Lean_NameHashSet_empty___closed__2);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instInhabited(void){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__2, &l_Lean_NameHashSet_empty___closed__2_once, _init_l_Lean_NameHashSet_empty___closed__2);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object* v_m_750_, lean_object* v_query_751_, lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
lean_object* v_zero_755_; uint8_t v_isZero_756_; 
v_zero_755_ = lean_unsigned_to_nat(0u);
v_isZero_756_ = lean_nat_dec_eq(v_x_753_, v_zero_755_);
if (v_isZero_756_ == 1)
{
lean_dec(v_x_754_);
lean_dec(v_x_753_);
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v___x_757_; 
v___x_757_ = lean_box(2);
return v___x_757_;
}
else
{
lean_object* v_val_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_val_758_ = lean_ctor_get(v_x_752_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_752_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v_x_752_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_val_758_);
lean_dec(v_x_752_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_val_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_keyArray_766_; lean_object* v_valueArray_767_; lean_object* v___x_768_; uint8_t v_isSome_769_; 
v_keyArray_766_ = lean_ctor_get(v_m_750_, 1);
v_valueArray_767_ = lean_ctor_get(v_m_750_, 2);
v___x_768_ = lean_array_fget_borrowed(v_keyArray_766_, v_x_754_);
v_isSome_769_ = lean_noption_is_some(v___x_768_);
if (v_isSome_769_ == 0)
{
lean_dec(v_x_753_);
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v_x_754_);
return v___x_770_;
}
else
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_x_754_);
v_val_771_ = lean_ctor_get(v_x_752_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_752_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v_x_752_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v_x_752_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_val_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_one_779_; lean_object* v_n_780_; lean_object* v___y_782_; 
v_one_779_ = lean_unsigned_to_nat(1u);
v_n_780_ = lean_nat_sub(v_x_753_, v_one_779_);
lean_dec(v_x_753_);
if (v_isSome_769_ == 0)
{
goto v___jp_788_;
}
else
{
lean_object* v___x_790_; uint8_t v_isSome_791_; 
v___x_790_ = lean_array_fget_borrowed(v_valueArray_767_, v_x_754_);
v_isSome_791_ = lean_noption_is_some(v___x_790_);
if (v_isSome_791_ == 0)
{
goto v___jp_788_;
}
else
{
lean_object* v_val_792_; uint8_t v___x_793_; 
lean_inc(v___x_768_);
v_val_792_ = lean_noption_get(v___x_768_);
v___x_793_ = lean_name_eq(v_val_792_, v_query_751_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
lean_dec(v_val_792_);
v___x_794_ = lean_array_get_size(v_keyArray_766_);
v___x_795_ = lean_nat_add(v_x_754_, v_one_779_);
lean_dec(v_x_754_);
v___x_796_ = lean_nat_dec_lt(v___x_795_, v___x_794_);
if (v___x_796_ == 0)
{
lean_dec(v___x_795_);
v_x_753_ = v_n_780_;
v_x_754_ = v_zero_755_;
goto _start;
}
else
{
v_x_753_ = v_n_780_;
v_x_754_ = v___x_795_;
goto _start;
}
}
else
{
lean_object* v_val_799_; lean_object* v___x_800_; 
lean_dec(v_n_780_);
lean_dec(v_x_752_);
lean_inc(v___x_790_);
v_val_799_ = lean_noption_get(v___x_790_);
v___x_800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_800_, 0, v_x_754_);
lean_ctor_set(v___x_800_, 1, v_val_792_);
lean_ctor_set(v___x_800_, 2, v_val_799_);
return v___x_800_;
}
}
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_783_ = lean_array_get_size(v_keyArray_766_);
v___x_784_ = lean_nat_add(v_x_754_, v_one_779_);
lean_dec(v_x_754_);
v___x_785_ = lean_nat_dec_lt(v___x_784_, v___x_783_);
if (v___x_785_ == 0)
{
lean_dec(v___x_784_);
v_x_752_ = v___y_782_;
v_x_753_ = v_n_780_;
v_x_754_ = v_zero_755_;
goto _start;
}
else
{
v_x_752_ = v___y_782_;
v_x_753_ = v_n_780_;
v_x_754_ = v___x_784_;
goto _start;
}
}
v___jp_788_:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v___x_789_; 
lean_inc(v_x_754_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_x_754_);
v___y_782_ = v___x_789_;
goto v___jp_781_;
}
else
{
v___y_782_ = v_x_752_;
goto v___jp_781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_m_801_, lean_object* v_query_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_m_801_, v_query_802_, v_x_803_, v_x_804_, v_x_805_);
lean_dec(v_query_802_);
lean_dec_ref(v_m_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object* v_m_807_, lean_object* v_query_808_){
_start:
{
lean_object* v_keyArray_809_; lean_object* v___x_810_; uint64_t v___y_812_; 
v_keyArray_809_ = lean_ctor_get(v_m_807_, 1);
v___x_810_ = lean_array_get_size(v_keyArray_809_);
if (lean_obj_tag(v_query_808_) == 0)
{
uint64_t v___x_827_; 
v___x_827_ = 1723ULL;
v___y_812_ = v___x_827_;
goto v___jp_811_;
}
else
{
uint64_t v_hash_828_; 
v_hash_828_ = lean_ctor_get_uint64(v_query_808_, sizeof(void*)*2);
v___y_812_ = v_hash_828_;
goto v___jp_811_;
}
v___jp_811_:
{
uint64_t v___x_813_; uint64_t v___x_814_; uint64_t v_fold_815_; uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_813_ = 32ULL;
v___x_814_ = lean_uint64_shift_right(v___y_812_, v___x_813_);
v_fold_815_ = lean_uint64_xor(v___y_812_, v___x_814_);
v___x_816_ = 16ULL;
v___x_817_ = lean_uint64_shift_right(v_fold_815_, v___x_816_);
v___x_818_ = lean_uint64_xor(v_fold_815_, v___x_817_);
v___x_819_ = lean_uint64_to_usize(v___x_818_);
v___x_820_ = lean_usize_of_nat(v___x_810_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_sub(v___x_820_, v___x_821_);
v___x_823_ = lean_usize_land(v___x_819_, v___x_822_);
v___x_824_ = lean_usize_to_nat(v___x_823_);
v___x_825_ = lean_box(0);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_m_807_, v_query_808_, v___x_825_, v___x_810_, v___x_824_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg___boxed(lean_object* v_m_829_, lean_object* v_query_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_829_, v_query_830_);
lean_dec(v_query_830_);
lean_dec_ref(v_m_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___redArg(lean_object* v_b_832_, lean_object* v_acc_833_, lean_object* v_i_834_){
_start:
{
lean_object* v___y_836_; lean_object* v_keyArray_844_; lean_object* v_valueArray_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_keyArray_844_ = lean_ctor_get(v_b_832_, 1);
v_valueArray_845_ = lean_ctor_get(v_b_832_, 2);
v___x_846_ = lean_array_get_size(v_keyArray_844_);
v___x_847_ = lean_nat_dec_lt(v_i_834_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_i_834_);
return v_acc_833_;
}
else
{
lean_object* v___x_848_; uint8_t v_isSome_849_; 
v___x_848_ = lean_array_fget_borrowed(v_keyArray_844_, v_i_834_);
v_isSome_849_ = lean_noption_is_some(v___x_848_);
if (v_isSome_849_ == 0)
{
goto v___jp_840_;
}
else
{
lean_object* v___x_850_; uint8_t v_isSome_851_; 
v___x_850_ = lean_array_fget_borrowed(v_valueArray_845_, v_i_834_);
v_isSome_851_ = lean_noption_is_some(v___x_850_);
if (v_isSome_851_ == 0)
{
goto v___jp_840_;
}
else
{
lean_object* v_val_852_; lean_object* v_val_853_; lean_object* v_i_855_; lean_object* v___x_860_; 
lean_inc(v___x_848_);
v_val_852_ = lean_noption_get(v___x_848_);
lean_inc(v___x_850_);
v_val_853_ = lean_noption_get(v___x_850_);
v___x_860_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(v_acc_833_, v_val_852_);
switch(lean_obj_tag(v___x_860_))
{
case 0:
{
lean_object* v_index_861_; lean_object* v_size_862_; lean_object* v___x_863_; 
v_index_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_index_861_);
lean_dec_ref_known(v___x_860_, 3);
v_size_862_ = lean_ctor_get(v_acc_833_, 0);
lean_inc(v_size_862_);
v___x_863_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_833_, v_size_862_, v_index_861_, v_val_852_, v_val_853_);
lean_dec(v_index_861_);
v___y_836_ = v___x_863_;
goto v___jp_835_;
}
case 1:
{
lean_object* v_index_864_; 
v_index_864_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_index_864_);
lean_dec_ref_known(v___x_860_, 1);
v_i_855_ = v_index_864_;
goto v___jp_854_;
}
default: 
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_833_, v___x_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_index_867_; 
v_index_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_index_867_);
lean_dec_ref_known(v___x_866_, 1);
v_i_855_ = v_index_867_;
goto v___jp_854_;
}
else
{
lean_dec(v_val_853_);
lean_dec(v_val_852_);
v___y_836_ = v_acc_833_;
goto v___jp_835_;
}
}
}
v___jp_854_:
{
lean_object* v_size_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_size_856_ = lean_ctor_get(v_acc_833_, 0);
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_nat_add(v_size_856_, v___x_857_);
v___x_859_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_833_, v___x_858_, v_i_855_, v_val_852_, v_val_853_);
lean_dec(v_i_855_);
v___y_836_ = v___x_859_;
goto v___jp_835_;
}
}
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_i_834_, v___x_837_);
lean_dec(v_i_834_);
v_acc_833_ = v___y_836_;
v_i_834_ = v___x_838_;
goto _start;
}
v___jp_840_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_i_834_, v___x_841_);
lean_dec(v_i_834_);
v_i_834_ = v___x_842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_868_, lean_object* v_acc_869_, lean_object* v_i_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___redArg(v_b_868_, v_acc_869_, v_i_870_);
lean_dec_ref(v_b_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___redArg(lean_object* v_init_872_, lean_object* v_b_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___redArg(v_b_873_, v_init_872_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___redArg___boxed(lean_object* v_init_876_, lean_object* v_b_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___redArg(v_init_876_, v_b_877_);
lean_dec_ref(v_b_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg(lean_object* v_m_879_){
_start:
{
lean_object* v_keyArray_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_cellCount_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v_target_887_; lean_object* v___x_888_; 
v_keyArray_880_ = lean_ctor_get(v_m_879_, 1);
v___x_881_ = lean_array_get_size(v_keyArray_880_);
v___x_882_ = lean_unsigned_to_nat(2u);
v_cellCount_883_ = lean_nat_mul(v___x_881_, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_883_);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_883_);
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_883_);
v_target_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_887_, 0, v___x_884_);
lean_ctor_set(v_target_887_, 1, v___x_885_);
lean_ctor_set(v_target_887_, 2, v___x_886_);
v___x_888_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___redArg(v_target_887_, v_m_879_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg___boxed(lean_object* v_m_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg(v_m_889_);
lean_dec_ref(v_m_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object* v_s_891_, lean_object* v_n_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___y_895_; lean_object* v_i_896_; lean_object* v___y_902_; lean_object* v___y_912_; lean_object* v_i_913_; lean_object* v___x_928_; 
v___x_893_ = lean_box(0);
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(v_s_891_, v_n_892_);
switch(lean_obj_tag(v___x_928_))
{
case 0:
{
lean_dec_ref_known(v___x_928_, 3);
lean_dec(v_n_892_);
return v_s_891_;
}
case 1:
{
lean_object* v_index_929_; lean_object* v_size_930_; lean_object* v_keyArray_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v_index_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_index_929_);
lean_dec_ref_known(v___x_928_, 1);
v_size_930_ = lean_ctor_get(v_s_891_, 0);
v_keyArray_931_ = lean_ctor_get(v_s_891_, 1);
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_add(v_size_930_, v___x_932_);
v___x_934_ = lean_array_get_size(v_keyArray_931_);
v___x_935_ = lean_nat_dec_lt(v___x_933_, v___x_934_);
if (v___x_935_ == 0)
{
lean_dec(v___x_933_);
lean_dec(v_index_929_);
goto v___jp_918_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_936_ = lean_unsigned_to_nat(4u);
v___x_937_ = lean_nat_mul(v___x_933_, v___x_936_);
v___x_938_ = lean_unsigned_to_nat(3u);
v___x_939_ = lean_nat_mul(v___x_934_, v___x_938_);
v___x_940_ = lean_nat_dec_le(v___x_937_, v___x_939_);
lean_dec(v___x_939_);
lean_dec(v___x_937_);
if (v___x_940_ == 0)
{
lean_dec(v___x_933_);
lean_dec(v_index_929_);
goto v___jp_918_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_891_, v___x_933_, v_index_929_, v_n_892_, v___x_893_);
lean_dec(v_index_929_);
return v___x_941_;
}
}
}
default: 
{
lean_object* v_size_942_; lean_object* v_keyArray_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_size_942_ = lean_ctor_get(v_s_891_, 0);
v_keyArray_943_ = lean_ctor_get(v_s_891_, 1);
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_size_942_, v___x_944_);
v___x_946_ = lean_array_get_size(v_keyArray_943_);
v___x_947_ = lean_nat_dec_lt(v___x_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_dec(v___x_945_);
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg(v_s_891_);
lean_dec_ref(v_s_891_);
v___y_902_ = v___x_948_;
goto v___jp_901_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_949_ = lean_unsigned_to_nat(4u);
v___x_950_ = lean_nat_mul(v___x_945_, v___x_949_);
lean_dec(v___x_945_);
v___x_951_ = lean_unsigned_to_nat(3u);
v___x_952_ = lean_nat_mul(v___x_946_, v___x_951_);
v___x_953_ = lean_nat_dec_le(v___x_950_, v___x_952_);
lean_dec(v___x_952_);
lean_dec(v___x_950_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg(v_s_891_);
lean_dec_ref(v_s_891_);
v___y_902_ = v___x_954_;
goto v___jp_901_;
}
else
{
v___y_902_ = v_s_891_;
goto v___jp_901_;
}
}
}
}
v___jp_894_:
{
lean_object* v_size_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_size_897_ = lean_ctor_get(v___y_895_, 0);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_size_897_, v___x_898_);
v___x_900_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_895_, v___x_899_, v_i_896_, v_n_892_, v___x_893_);
lean_dec(v_i_896_);
return v___x_900_;
}
v___jp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(v___y_902_, v_n_892_);
switch(lean_obj_tag(v___x_903_))
{
case 0:
{
lean_object* v_index_904_; lean_object* v_size_905_; lean_object* v___x_906_; 
v_index_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_index_904_);
lean_dec_ref_known(v___x_903_, 3);
v_size_905_ = lean_ctor_get(v___y_902_, 0);
lean_inc(v_size_905_);
v___x_906_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_902_, v_size_905_, v_index_904_, v_n_892_, v___x_893_);
lean_dec(v_index_904_);
return v___x_906_;
}
case 1:
{
lean_object* v_index_907_; 
v_index_907_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_index_907_);
lean_dec_ref_known(v___x_903_, 1);
v___y_895_ = v___y_902_;
v_i_896_ = v_index_907_;
goto v___jp_894_;
}
default: 
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_902_, v___x_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_index_910_; 
v_index_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_index_910_);
lean_dec_ref_known(v___x_909_, 1);
v___y_895_ = v___y_902_;
v_i_896_ = v_index_910_;
goto v___jp_894_;
}
else
{
lean_dec(v_n_892_);
return v___y_902_;
}
}
}
}
v___jp_911_:
{
lean_object* v_size_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_size_914_ = lean_ctor_get(v___y_912_, 0);
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_size_914_, v___x_915_);
v___x_917_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_912_, v___x_916_, v_i_913_, v_n_892_, v___x_893_);
lean_dec(v_i_913_);
return v___x_917_;
}
v___jp_918_:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg(v_s_891_);
lean_dec_ref(v_s_891_);
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(v___x_919_, v_n_892_);
switch(lean_obj_tag(v___x_920_))
{
case 0:
{
lean_object* v_index_921_; lean_object* v_size_922_; lean_object* v___x_923_; 
v_index_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_index_921_);
lean_dec_ref_known(v___x_920_, 3);
v_size_922_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_size_922_);
v___x_923_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_919_, v_size_922_, v_index_921_, v_n_892_, v___x_893_);
lean_dec(v_index_921_);
return v___x_923_;
}
case 1:
{
lean_object* v_index_924_; 
v_index_924_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_index_924_);
lean_dec_ref_known(v___x_920_, 1);
v___y_912_ = v___x_919_;
v_i_913_ = v_index_924_;
goto v___jp_911_;
}
default: 
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_919_, v___x_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_index_927_; 
v_index_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_index_927_);
lean_dec_ref_known(v___x_926_, 1);
v___y_912_ = v___x_919_;
v_i_913_ = v_index_927_;
goto v___jp_911_;
}
else
{
lean_dec(v_n_892_);
return v___x_919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0(lean_object* v_00_u03b2_955_, lean_object* v_m_956_, lean_object* v_query_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_956_, v_query_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___boxed(lean_object* v_00_u03b2_959_, lean_object* v_m_960_, lean_object* v_query_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0(v_00_u03b2_959_, v_m_960_, v_query_961_);
lean_dec(v_query_961_);
lean_dec_ref(v_m_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1(lean_object* v_00_u03b2_963_, lean_object* v_m_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___redArg(v_m_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1___boxed(lean_object* v_00_u03b2_966_, lean_object* v_m_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1(v_00_u03b2_966_, v_m_967_);
lean_dec_ref(v_m_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_969_, lean_object* v_m_970_, lean_object* v_query_971_, lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_m_970_, v_query_971_, v_x_972_, v_x_973_, v_x_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_977_, lean_object* v_m_978_, lean_object* v_query_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0_spec__0(v_00_u03b2_977_, v_m_978_, v_query_979_, v_x_980_, v_x_981_, v_x_982_, v_x_983_);
lean_dec(v_query_979_);
lean_dec_ref(v_m_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2(lean_object* v_00_u03b2_985_, lean_object* v_init_986_, lean_object* v_b_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___redArg(v_init_986_, v_b_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2___boxed(lean_object* v_00_u03b2_989_, lean_object* v_init_990_, lean_object* v_b_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2(v_00_u03b2_989_, v_init_990_, v_b_991_);
lean_dec_ref(v_b_991_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_993_, lean_object* v_b_994_, lean_object* v_acc_995_, lean_object* v_i_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___redArg(v_b_994_, v_acc_995_, v_i_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_998_, lean_object* v_b_999_, lean_object* v_acc_1000_, lean_object* v_i_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_NameHashSet_insert_spec__1_spec__2_spec__3(v_00_u03b2_998_, v_b_999_, v_acc_1000_, v_i_1001_);
lean_dec_ref(v_b_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___redArg(lean_object* v_m_1003_, lean_object* v_query_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_1003_, v_query_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_index_1006_; lean_object* v_key_1007_; lean_object* v_value_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
v_index_1006_ = lean_ctor_get(v___x_1005_, 0);
v_key_1007_ = lean_ctor_get(v___x_1005_, 1);
v_value_1008_ = lean_ctor_get(v___x_1005_, 2);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1005_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_value_1008_);
lean_inc(v_key_1007_);
lean_inc(v_index_1006_);
lean_dec(v___x_1005_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_index_1006_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_key_1007_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_value_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v___x_1016_; 
lean_dec(v___x_1005_);
v___x_1016_ = lean_box(1);
return v___x_1016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___redArg___boxed(lean_object* v_m_1017_, lean_object* v_query_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___redArg(v_m_1017_, v_query_1018_);
lean_dec(v_query_1018_);
lean_dec_ref(v_m_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object* v_m_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___redArg(v_m_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1022_) == 0)
{
uint8_t v___x_1023_; 
lean_dec_ref_known(v___x_1022_, 3);
v___x_1023_ = 1;
return v___x_1023_;
}
else
{
uint8_t v___x_1024_; 
v___x_1024_ = 0;
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object* v_m_1025_, lean_object* v_a_1026_){
_start:
{
uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_res_1027_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_m_1025_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object* v_s_1029_, lean_object* v_n_1030_){
_start:
{
uint8_t v___x_1031_; 
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_s_1029_, v_n_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object* v_s_1032_, lean_object* v_n_1033_){
_start:
{
uint8_t v_res_1034_; lean_object* v_r_1035_; 
v_res_1034_ = l_Lean_NameHashSet_contains(v_s_1032_, v_n_1033_);
lean_dec(v_n_1033_);
lean_dec_ref(v_s_1032_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object* v_00_u03b2_1036_, lean_object* v_m_1037_, lean_object* v_a_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_1037_, v_a_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object* v_00_u03b2_1040_, lean_object* v_m_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_res_1043_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(v_00_u03b2_1040_, v_m_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_m_1041_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0(lean_object* v_00_u03b2_1045_, lean_object* v_m_1046_, lean_object* v_query_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___redArg(v_m_1046_, v_query_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_m_1050_, lean_object* v_query_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_spec__0(v_00_u03b2_1049_, v_m_1050_, v_query_1051_);
lean_dec(v_query_1051_);
lean_dec_ref(v_m_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___lam__0(lean_object* v_f_1053_, lean_object* v_k_1054_, lean_object* v_v_1055_){
_start:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = lean_apply_1(v_f_1053_, v_k_1054_);
v___x_1057_ = lean_unbox(v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_box(0);
return v___x_1058_;
}
else
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_v_1055_);
return v___x_1059_;
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_noption_none();
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object* v_f_1061_, lean_object* v_m_1062_){
_start:
{
lean_object* v_keyArray_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_keyArray_1063_ = lean_ctor_get(v_m_1062_, 1);
v___f_1064_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___lam__0), 3, 1);
lean_closure_set(v___f_1064_, 0, v_f_1061_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_array_get_size(v_keyArray_1063_);
v___x_1067_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___closed__0);
v___x_1068_ = lean_mk_array(v___x_1066_, v___x_1067_);
lean_inc_ref(v_keyArray_1063_);
v___x_1069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1065_);
lean_ctor_set(v___x_1069_, 1, v_keyArray_1063_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
v___x_1070_ = l_Std_DHashMap_Internal_Raw_u2080_filterMapLoop___redArg(v___f_1064_, v_m_1062_, v___x_1069_, v___x_1065_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0___boxed(lean_object* v_f_1071_, lean_object* v_m_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_1071_, v_m_1072_);
lean_dec_ref(v_m_1072_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object* v_f_1074_, lean_object* v_s_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_1074_, v_s_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter___boxed(lean_object* v_f_1077_, lean_object* v_s_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_NameHashSet_filter(v_f_1077_, v_s_1078_);
lean_dec_ref(v_s_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object* v_f_1080_, lean_object* v_m_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_1080_, v_m_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0___boxed(lean_object* v_f_1083_, lean_object* v_m_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(v_f_1083_, v_m_1084_);
lean_dec_ref(v_m_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
if (lean_obj_tag(v_x_1087_) == 0)
{
uint8_t v___x_1088_; 
v___x_1088_ = 1;
return v___x_1088_;
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = 0;
return v___x_1089_;
}
}
else
{
if (lean_obj_tag(v_x_1087_) == 0)
{
uint8_t v___x_1090_; 
v___x_1090_ = 0;
return v___x_1090_;
}
else
{
lean_object* v_head_1091_; lean_object* v_tail_1092_; lean_object* v_head_1093_; lean_object* v_tail_1094_; uint8_t v___x_1095_; 
v_head_1091_ = lean_ctor_get(v_x_1086_, 0);
v_tail_1092_ = lean_ctor_get(v_x_1086_, 1);
v_head_1093_ = lean_ctor_get(v_x_1087_, 0);
v_tail_1094_ = lean_ctor_get(v_x_1087_, 1);
v___x_1095_ = lean_nat_dec_eq(v_head_1091_, v_head_1093_);
if (v___x_1095_ == 0)
{
return v___x_1095_;
}
else
{
v_x_1086_ = v_tail_1092_;
v_x_1087_ = v_tail_1094_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_res_1099_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_1097_, v_x_1098_);
lean_dec(v_x_1098_);
lean_dec(v_x_1097_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object* v_v_u2081_1101_, lean_object* v_v_u2082_1102_){
_start:
{
lean_object* v_name_1103_; lean_object* v_imported_1104_; lean_object* v_ctx_1105_; lean_object* v_scopes_1106_; lean_object* v_name_1107_; lean_object* v_imported_1108_; lean_object* v_ctx_1109_; lean_object* v_scopes_1110_; uint8_t v___y_1112_; uint8_t v___x_1115_; 
v_name_1103_ = lean_ctor_get(v_v_u2081_1101_, 0);
v_imported_1104_ = lean_ctor_get(v_v_u2081_1101_, 1);
v_ctx_1105_ = lean_ctor_get(v_v_u2081_1101_, 2);
v_scopes_1106_ = lean_ctor_get(v_v_u2081_1101_, 3);
v_name_1107_ = lean_ctor_get(v_v_u2082_1102_, 0);
v_imported_1108_ = lean_ctor_get(v_v_u2082_1102_, 1);
v_ctx_1109_ = lean_ctor_get(v_v_u2082_1102_, 2);
v_scopes_1110_ = lean_ctor_get(v_v_u2082_1102_, 3);
v___x_1115_ = l_Lean_Name_isPrefixOf(v_name_1103_, v_name_1107_);
if (v___x_1115_ == 0)
{
v___y_1112_ = v___x_1115_;
goto v___jp_1111_;
}
else
{
uint8_t v___x_1116_; 
v___x_1116_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1106_, v_scopes_1110_);
v___y_1112_ = v___x_1116_;
goto v___jp_1111_;
}
v___jp_1111_:
{
if (v___y_1112_ == 0)
{
return v___y_1112_;
}
else
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_name_eq(v_ctx_1105_, v_ctx_1109_);
if (v___x_1113_ == 0)
{
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_name_eq(v_imported_1104_, v_imported_1108_);
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object* v_v_u2081_1117_, lean_object* v_v_u2082_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_1117_, v_v_u2082_1118_);
lean_dec_ref(v_v_u2082_1118_);
lean_dec_ref(v_v_u2081_1117_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object* v_v_u2081_1121_, lean_object* v_v_u2082_1122_){
_start:
{
lean_object* v_name_1123_; lean_object* v_imported_1124_; lean_object* v_ctx_1125_; lean_object* v_scopes_1126_; lean_object* v_name_1127_; lean_object* v_imported_1128_; lean_object* v_ctx_1129_; lean_object* v_scopes_1130_; uint8_t v___y_1132_; uint8_t v___x_1135_; 
v_name_1123_ = lean_ctor_get(v_v_u2081_1121_, 0);
v_imported_1124_ = lean_ctor_get(v_v_u2081_1121_, 1);
v_ctx_1125_ = lean_ctor_get(v_v_u2081_1121_, 2);
v_scopes_1126_ = lean_ctor_get(v_v_u2081_1121_, 3);
v_name_1127_ = lean_ctor_get(v_v_u2082_1122_, 0);
v_imported_1128_ = lean_ctor_get(v_v_u2082_1122_, 1);
v_ctx_1129_ = lean_ctor_get(v_v_u2082_1122_, 2);
v_scopes_1130_ = lean_ctor_get(v_v_u2082_1122_, 3);
v___x_1135_ = l_Lean_Name_isSuffixOf(v_name_1123_, v_name_1127_);
if (v___x_1135_ == 0)
{
v___y_1132_ = v___x_1135_;
goto v___jp_1131_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1126_, v_scopes_1130_);
v___y_1132_ = v___x_1136_;
goto v___jp_1131_;
}
v___jp_1131_:
{
if (v___y_1132_ == 0)
{
return v___y_1132_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_name_eq(v_ctx_1125_, v_ctx_1129_);
if (v___x_1133_ == 0)
{
return v___x_1133_;
}
else
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_name_eq(v_imported_1124_, v_imported_1128_);
return v___x_1134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object* v_v_u2081_1137_, lean_object* v_v_u2082_1138_){
_start:
{
uint8_t v_res_1139_; lean_object* v_r_1140_; 
v_res_1139_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_1137_, v_v_u2082_1138_);
lean_dec_ref(v_v_u2082_1138_);
lean_dec_ref(v_v_u2081_1137_);
v_r_1140_ = lean_box(v_res_1139_);
return v_r_1140_;
}
}
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_SSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_SSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_NameSet_empty = _init_l_Lean_NameSet_empty();
lean_mark_persistent(l_Lean_NameSet_empty);
l_Lean_NameSet_instEmptyCollection = _init_l_Lean_NameSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameSet_instEmptyCollection);
l_Lean_NameSet_instInhabited = _init_l_Lean_NameSet_instInhabited();
lean_mark_persistent(l_Lean_NameSet_instInhabited);
l_Lean_NameSSet_empty = _init_l_Lean_NameSSet_empty();
lean_mark_persistent(l_Lean_NameSSet_empty);
l_Lean_NameSSet_instEmptyCollection = _init_l_Lean_NameSSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameSSet_instEmptyCollection);
l_Lean_NameSSet_instInhabited = _init_l_Lean_NameSSet_instInhabited();
lean_mark_persistent(l_Lean_NameSSet_instInhabited);
l_Lean_NameHashSet_empty = _init_l_Lean_NameHashSet_empty();
lean_mark_persistent(l_Lean_NameHashSet_empty);
l_Lean_NameHashSet_instEmptyCollection = _init_l_Lean_NameHashSet_instEmptyCollection();
lean_mark_persistent(l_Lean_NameHashSet_instEmptyCollection);
l_Lean_NameHashSet_instInhabited = _init_l_Lean_NameHashSet_instInhabited();
lean_mark_persistent(l_Lean_NameHashSet_instInhabited);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_NameMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_SSet(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_NameMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
