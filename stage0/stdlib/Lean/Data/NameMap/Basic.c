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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_NameHashSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameHashSet_instInhabited;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object*, lean_object*);
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
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = lean_unsigned_to_nat(16u);
v___x_741_ = lean_mk_array(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__0, &l_Lean_NameHashSet_empty___closed__0_once, _init_l_Lean_NameHashSet_empty___closed__0);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty(void){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instInhabited(void){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_747_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object* v_a_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_749_) == 0)
{
uint8_t v___x_750_; 
v___x_750_ = 0;
return v___x_750_;
}
else
{
lean_object* v_key_751_; lean_object* v_tail_752_; uint8_t v___x_753_; 
v_key_751_ = lean_ctor_get(v_x_749_, 0);
v_tail_752_ = lean_ctor_get(v_x_749_, 2);
v___x_753_ = lean_name_eq(v_key_751_, v_a_748_);
if (v___x_753_ == 0)
{
v_x_749_ = v_tail_752_;
goto _start;
}
else
{
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_755_, lean_object* v_x_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_755_, v_x_756_);
lean_dec(v_x_756_);
lean_dec(v_a_755_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
return v_x_759_;
}
else
{
lean_object* v_key_761_; lean_object* v_value_762_; lean_object* v_tail_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_789_; 
v_key_761_ = lean_ctor_get(v_x_760_, 0);
v_value_762_ = lean_ctor_get(v_x_760_, 1);
v_tail_763_ = lean_ctor_get(v_x_760_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_789_ == 0)
{
v___x_765_ = v_x_760_;
v_isShared_766_ = v_isSharedCheck_789_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_tail_763_);
lean_inc(v_value_762_);
lean_inc(v_key_761_);
lean_dec(v_x_760_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_789_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; uint64_t v___y_769_; 
v___x_767_ = lean_array_get_size(v_x_759_);
if (lean_obj_tag(v_key_761_) == 0)
{
uint64_t v___x_787_; 
v___x_787_ = 1723ULL;
v___y_769_ = v___x_787_;
goto v___jp_768_;
}
else
{
uint64_t v_hash_788_; 
v_hash_788_ = lean_ctor_get_uint64(v_key_761_, sizeof(void*)*2);
v___y_769_ = v_hash_788_;
goto v___jp_768_;
}
v___jp_768_:
{
uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v_fold_772_; uint64_t v___x_773_; uint64_t v___x_774_; uint64_t v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_770_ = 32ULL;
v___x_771_ = lean_uint64_shift_right(v___y_769_, v___x_770_);
v_fold_772_ = lean_uint64_xor(v___y_769_, v___x_771_);
v___x_773_ = 16ULL;
v___x_774_ = lean_uint64_shift_right(v_fold_772_, v___x_773_);
v___x_775_ = lean_uint64_xor(v_fold_772_, v___x_774_);
v___x_776_ = lean_uint64_to_usize(v___x_775_);
v___x_777_ = lean_usize_of_nat(v___x_767_);
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_sub(v___x_777_, v___x_778_);
v___x_780_ = lean_usize_land(v___x_776_, v___x_779_);
v___x_781_ = lean_array_uget_borrowed(v_x_759_, v___x_780_);
lean_inc(v___x_781_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 2, v___x_781_);
v___x_783_ = v___x_765_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_key_761_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_value_762_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v___x_781_);
v___x_783_ = v_reuseFailAlloc_786_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; 
v___x_784_ = lean_array_uset(v_x_759_, v___x_780_, v___x_783_);
v_x_759_ = v___x_784_;
v_x_760_ = v_tail_763_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_790_, lean_object* v_source_791_, lean_object* v_target_792_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_source_791_);
v___x_794_ = lean_nat_dec_lt(v_i_790_, v___x_793_);
if (v___x_794_ == 0)
{
lean_dec_ref(v_source_791_);
lean_dec(v_i_790_);
return v_target_792_;
}
else
{
lean_object* v_es_795_; lean_object* v___x_796_; lean_object* v_source_797_; lean_object* v_target_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_es_795_ = lean_array_fget(v_source_791_, v_i_790_);
v___x_796_ = lean_box(0);
v_source_797_ = lean_array_fset(v_source_791_, v_i_790_, v___x_796_);
v_target_798_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_792_, v_es_795_);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_i_790_, v___x_799_);
lean_dec(v_i_790_);
v_i_790_ = v___x_800_;
v_source_791_ = v_source_797_;
v_target_792_ = v_target_798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(lean_object* v_data_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v_nbuckets_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_803_ = lean_array_get_size(v_data_802_);
v___x_804_ = lean_unsigned_to_nat(2u);
v_nbuckets_805_ = lean_nat_mul(v___x_803_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_box(0);
v___x_808_ = lean_mk_array(v_nbuckets_805_, v___x_807_);
v___x_809_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v___x_806_, v_data_802_, v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_b_812_){
_start:
{
lean_object* v_size_813_; lean_object* v_buckets_814_; lean_object* v___x_815_; uint64_t v___y_817_; 
v_size_813_ = lean_ctor_get(v_m_810_, 0);
v_buckets_814_ = lean_ctor_get(v_m_810_, 1);
v___x_815_ = lean_array_get_size(v_buckets_814_);
if (lean_obj_tag(v_a_811_) == 0)
{
uint64_t v___x_854_; 
v___x_854_ = 1723ULL;
v___y_817_ = v___x_854_;
goto v___jp_816_;
}
else
{
uint64_t v_hash_855_; 
v_hash_855_ = lean_ctor_get_uint64(v_a_811_, sizeof(void*)*2);
v___y_817_ = v_hash_855_;
goto v___jp_816_;
}
v___jp_816_:
{
uint64_t v___x_818_; uint64_t v___x_819_; uint64_t v_fold_820_; uint64_t v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v___x_828_; lean_object* v_bkt_829_; uint8_t v___x_830_; 
v___x_818_ = 32ULL;
v___x_819_ = lean_uint64_shift_right(v___y_817_, v___x_818_);
v_fold_820_ = lean_uint64_xor(v___y_817_, v___x_819_);
v___x_821_ = 16ULL;
v___x_822_ = lean_uint64_shift_right(v_fold_820_, v___x_821_);
v___x_823_ = lean_uint64_xor(v_fold_820_, v___x_822_);
v___x_824_ = lean_uint64_to_usize(v___x_823_);
v___x_825_ = lean_usize_of_nat(v___x_815_);
v___x_826_ = ((size_t)1ULL);
v___x_827_ = lean_usize_sub(v___x_825_, v___x_826_);
v___x_828_ = lean_usize_land(v___x_824_, v___x_827_);
v_bkt_829_ = lean_array_uget_borrowed(v_buckets_814_, v___x_828_);
v___x_830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_811_, v_bkt_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_851_; 
lean_inc_ref(v_buckets_814_);
lean_inc(v_size_813_);
v_isSharedCheck_851_ = !lean_is_exclusive(v_m_810_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; lean_object* v_unused_853_; 
v_unused_852_ = lean_ctor_get(v_m_810_, 1);
lean_dec(v_unused_852_);
v_unused_853_ = lean_ctor_get(v_m_810_, 0);
lean_dec(v_unused_853_);
v___x_832_ = v_m_810_;
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
else
{
lean_dec(v_m_810_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_851_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v_size_x27_835_; lean_object* v___x_836_; lean_object* v_buckets_x27_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_834_ = lean_unsigned_to_nat(1u);
v_size_x27_835_ = lean_nat_add(v_size_813_, v___x_834_);
lean_dec(v_size_813_);
lean_inc(v_bkt_829_);
v___x_836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_836_, 0, v_a_811_);
lean_ctor_set(v___x_836_, 1, v_b_812_);
lean_ctor_set(v___x_836_, 2, v_bkt_829_);
v_buckets_x27_837_ = lean_array_uset(v_buckets_814_, v___x_828_, v___x_836_);
v___x_838_ = lean_unsigned_to_nat(4u);
v___x_839_ = lean_nat_mul(v_size_x27_835_, v___x_838_);
v___x_840_ = lean_unsigned_to_nat(3u);
v___x_841_ = lean_nat_div(v___x_839_, v___x_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_array_get_size(v_buckets_x27_837_);
v___x_843_ = lean_nat_dec_le(v___x_841_, v___x_842_);
lean_dec(v___x_841_);
if (v___x_843_ == 0)
{
lean_object* v_val_844_; lean_object* v___x_846_; 
v_val_844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_buckets_x27_837_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_val_844_);
lean_ctor_set(v___x_832_, 0, v_size_x27_835_);
v___x_846_ = v___x_832_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_size_x27_835_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_val_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v___x_849_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_buckets_x27_837_);
lean_ctor_set(v___x_832_, 0, v_size_x27_835_);
v___x_849_ = v___x_832_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_size_x27_835_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_buckets_x27_837_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_dec(v_b_812_);
lean_dec(v_a_811_);
return v_m_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object* v_s_856_, lean_object* v_n_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_box(0);
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_s_856_, v_n_857_, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(lean_object* v_00_u03b2_860_, lean_object* v_m_861_, lean_object* v_a_862_, lean_object* v_b_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_861_, v_a_862_, v_b_863_);
return v___x_864_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_865_, lean_object* v_a_866_, lean_object* v_x_867_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_869_, lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(v_00_u03b2_869_, v_a_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec(v_a_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(lean_object* v_00_u03b2_874_, lean_object* v_data_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_data_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_877_, lean_object* v_i_878_, lean_object* v_source_879_, lean_object* v_target_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v_i_878_, v_source_879_, v_target_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object* v_m_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_buckets_888_; lean_object* v___x_889_; uint64_t v___y_891_; 
v_buckets_888_ = lean_ctor_get(v_m_886_, 1);
v___x_889_ = lean_array_get_size(v_buckets_888_);
if (lean_obj_tag(v_a_887_) == 0)
{
uint64_t v___x_905_; 
v___x_905_ = 1723ULL;
v___y_891_ = v___x_905_;
goto v___jp_890_;
}
else
{
uint64_t v_hash_906_; 
v_hash_906_ = lean_ctor_get_uint64(v_a_887_, sizeof(void*)*2);
v___y_891_ = v_hash_906_;
goto v___jp_890_;
}
v___jp_890_:
{
uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v_fold_894_; uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_892_ = 32ULL;
v___x_893_ = lean_uint64_shift_right(v___y_891_, v___x_892_);
v_fold_894_ = lean_uint64_xor(v___y_891_, v___x_893_);
v___x_895_ = 16ULL;
v___x_896_ = lean_uint64_shift_right(v_fold_894_, v___x_895_);
v___x_897_ = lean_uint64_xor(v_fold_894_, v___x_896_);
v___x_898_ = lean_uint64_to_usize(v___x_897_);
v___x_899_ = lean_usize_of_nat(v___x_889_);
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_sub(v___x_899_, v___x_900_);
v___x_902_ = lean_usize_land(v___x_898_, v___x_901_);
v___x_903_ = lean_array_uget_borrowed(v_buckets_888_, v___x_902_);
v___x_904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_887_, v___x_903_);
return v___x_904_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_m_907_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object* v_s_911_, lean_object* v_n_912_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_s_911_, v_n_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object* v_s_914_, lean_object* v_n_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_Lean_NameHashSet_contains(v_s_914_, v_n_915_);
lean_dec(v_n_915_);
lean_dec_ref(v_s_914_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object* v_00_u03b2_918_, lean_object* v_m_919_, lean_object* v_a_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_919_, v_a_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object* v_00_u03b2_922_, lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(v_00_u03b2_922_, v_m_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_m_923_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object* v_f_927_, lean_object* v_acc_928_, lean_object* v_a_929_){
_start:
{
if (lean_obj_tag(v_a_929_) == 0)
{
lean_dec_ref(v_f_927_);
return v_acc_928_;
}
else
{
lean_object* v_key_930_; lean_object* v_value_931_; lean_object* v_tail_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_943_; 
v_key_930_ = lean_ctor_get(v_a_929_, 0);
v_value_931_ = lean_ctor_get(v_a_929_, 1);
v_tail_932_ = lean_ctor_get(v_a_929_, 2);
v_isSharedCheck_943_ = !lean_is_exclusive(v_a_929_);
if (v_isSharedCheck_943_ == 0)
{
v___x_934_ = v_a_929_;
v_isShared_935_ = v_isSharedCheck_943_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_tail_932_);
lean_inc(v_value_931_);
lean_inc(v_key_930_);
lean_dec(v_a_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_943_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; uint8_t v___x_937_; 
lean_inc_ref(v_f_927_);
lean_inc(v_key_930_);
v___x_936_ = lean_apply_1(v_f_927_, v_key_930_);
v___x_937_ = lean_unbox(v___x_936_);
if (v___x_937_ == 0)
{
lean_del_object(v___x_934_);
lean_dec(v_value_931_);
lean_dec(v_key_930_);
v_a_929_ = v_tail_932_;
goto _start;
}
else
{
lean_object* v___x_940_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 2, v_acc_928_);
v___x_940_ = v___x_934_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_key_930_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_value_931_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_acc_928_);
v___x_940_ = v_reuseFailAlloc_942_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
v_acc_928_ = v___x_940_;
v_a_929_ = v_tail_932_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(lean_object* v_f_944_, size_t v_sz_945_, size_t v_i_946_, lean_object* v_bs_947_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_946_, v_sz_945_);
if (v___x_948_ == 0)
{
lean_dec_ref(v_f_944_);
return v_bs_947_;
}
else
{
lean_object* v_v_949_; lean_object* v___x_950_; lean_object* v_bs_x27_951_; lean_object* v___x_952_; lean_object* v___x_953_; size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
v_v_949_ = lean_array_uget(v_bs_947_, v_i_946_);
v___x_950_ = lean_unsigned_to_nat(0u);
v_bs_x27_951_ = lean_array_uset(v_bs_947_, v_i_946_, v___x_950_);
v___x_952_ = lean_box(0);
lean_inc_ref(v_f_944_);
v___x_953_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_944_, v___x_952_, v_v_949_);
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_946_, v___x_954_);
v___x_956_ = lean_array_uset(v_bs_x27_951_, v_i_946_, v___x_953_);
v_i_946_ = v___x_955_;
v_bs_947_ = v___x_956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(lean_object* v_f_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_bs_961_){
_start:
{
size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v_sz_boxed_962_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_963_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_958_, v_sz_boxed_962_, v_i_boxed_963_, v_bs_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(lean_object* v_as_965_, size_t v_i_966_, size_t v_stop_967_, lean_object* v_b_968_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = lean_usize_dec_eq(v_i_966_, v_stop_967_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; size_t v___x_973_; size_t v___x_974_; 
v___x_970_ = lean_array_uget_borrowed(v_as_965_, v_i_966_);
v___x_971_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_970_);
v___x_972_ = lean_nat_add(v_b_968_, v___x_971_);
lean_dec(v___x_971_);
lean_dec(v_b_968_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_966_, v___x_973_);
v_i_966_ = v___x_974_;
v_b_968_ = v___x_972_;
goto _start;
}
else
{
return v_b_968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(lean_object* v_as_976_, lean_object* v_i_977_, lean_object* v_stop_978_, lean_object* v_b_979_){
_start:
{
size_t v_i_boxed_980_; size_t v_stop_boxed_981_; lean_object* v_res_982_; 
v_i_boxed_980_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_stop_boxed_981_ = lean_unbox_usize(v_stop_978_);
lean_dec(v_stop_978_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_as_976_, v_i_boxed_980_, v_stop_boxed_981_, v_b_979_);
lean_dec_ref(v_as_976_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object* v_f_983_, lean_object* v_m_984_){
_start:
{
lean_object* v_buckets_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1012_; 
v_buckets_985_ = lean_ctor_get(v_m_984_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_m_984_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_m_984_, 0);
lean_dec(v_unused_1013_);
v___x_987_ = v_m_984_;
v_isShared_988_ = v_isSharedCheck_1012_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_buckets_985_);
lean_dec(v_m_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1012_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
size_t v_sz_989_; size_t v___x_990_; lean_object* v_newBuckets_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_sz_989_ = lean_array_size(v_buckets_985_);
v___x_990_ = ((size_t)0ULL);
v_newBuckets_991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_983_, v_sz_989_, v___x_990_, v_buckets_985_);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_array_get_size(v_newBuckets_991_);
v___x_994_ = lean_nat_dec_lt(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_996_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_992_);
v___x_996_ = v___x_987_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_newBuckets_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
uint8_t v___x_998_; 
v___x_998_ = lean_nat_dec_le(v___x_993_, v___x_993_);
if (v___x_998_ == 0)
{
if (v___x_994_ == 0)
{
lean_object* v___x_1000_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_992_);
v___x_1000_ = v___x_987_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_newBuckets_991_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1002_ = lean_usize_of_nat(v___x_993_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_991_, v___x_990_, v___x_1002_, v___x_992_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_1003_);
v___x_1005_ = v___x_987_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_newBuckets_991_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
size_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = lean_usize_of_nat(v___x_993_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_991_, v___x_990_, v___x_1007_, v___x_992_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_1008_);
v___x_1010_ = v___x_987_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_newBuckets_991_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object* v_f_1014_, lean_object* v_s_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(v_f_1014_, v_s_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
if (lean_obj_tag(v_x_1017_) == 0)
{
if (lean_obj_tag(v_x_1018_) == 0)
{
uint8_t v___x_1019_; 
v___x_1019_ = 1;
return v___x_1019_;
}
else
{
uint8_t v___x_1020_; 
v___x_1020_ = 0;
return v___x_1020_;
}
}
else
{
if (lean_obj_tag(v_x_1018_) == 0)
{
uint8_t v___x_1021_; 
v___x_1021_ = 0;
return v___x_1021_;
}
else
{
lean_object* v_head_1022_; lean_object* v_tail_1023_; lean_object* v_head_1024_; lean_object* v_tail_1025_; uint8_t v___x_1026_; 
v_head_1022_ = lean_ctor_get(v_x_1017_, 0);
v_tail_1023_ = lean_ctor_get(v_x_1017_, 1);
v_head_1024_ = lean_ctor_get(v_x_1018_, 0);
v_tail_1025_ = lean_ctor_get(v_x_1018_, 1);
v___x_1026_ = lean_nat_dec_eq(v_head_1022_, v_head_1024_);
if (v___x_1026_ == 0)
{
return v___x_1026_;
}
else
{
v_x_1017_ = v_tail_1023_;
v_x_1018_ = v_tail_1025_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_1028_, v_x_1029_);
lean_dec(v_x_1029_);
lean_dec(v_x_1028_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object* v_v_u2081_1032_, lean_object* v_v_u2082_1033_){
_start:
{
lean_object* v_name_1034_; lean_object* v_imported_1035_; lean_object* v_ctx_1036_; lean_object* v_scopes_1037_; lean_object* v_name_1038_; lean_object* v_imported_1039_; lean_object* v_ctx_1040_; lean_object* v_scopes_1041_; uint8_t v___y_1043_; uint8_t v___x_1046_; 
v_name_1034_ = lean_ctor_get(v_v_u2081_1032_, 0);
v_imported_1035_ = lean_ctor_get(v_v_u2081_1032_, 1);
v_ctx_1036_ = lean_ctor_get(v_v_u2081_1032_, 2);
v_scopes_1037_ = lean_ctor_get(v_v_u2081_1032_, 3);
v_name_1038_ = lean_ctor_get(v_v_u2082_1033_, 0);
v_imported_1039_ = lean_ctor_get(v_v_u2082_1033_, 1);
v_ctx_1040_ = lean_ctor_get(v_v_u2082_1033_, 2);
v_scopes_1041_ = lean_ctor_get(v_v_u2082_1033_, 3);
v___x_1046_ = l_Lean_Name_isPrefixOf(v_name_1034_, v_name_1038_);
if (v___x_1046_ == 0)
{
v___y_1043_ = v___x_1046_;
goto v___jp_1042_;
}
else
{
uint8_t v___x_1047_; 
v___x_1047_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1037_, v_scopes_1041_);
v___y_1043_ = v___x_1047_;
goto v___jp_1042_;
}
v___jp_1042_:
{
if (v___y_1043_ == 0)
{
return v___y_1043_;
}
else
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_name_eq(v_ctx_1036_, v_ctx_1040_);
if (v___x_1044_ == 0)
{
return v___x_1044_;
}
else
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_name_eq(v_imported_1035_, v_imported_1039_);
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object* v_v_u2081_1048_, lean_object* v_v_u2082_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_1048_, v_v_u2082_1049_);
lean_dec_ref(v_v_u2082_1049_);
lean_dec_ref(v_v_u2081_1048_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object* v_v_u2081_1052_, lean_object* v_v_u2082_1053_){
_start:
{
lean_object* v_name_1054_; lean_object* v_imported_1055_; lean_object* v_ctx_1056_; lean_object* v_scopes_1057_; lean_object* v_name_1058_; lean_object* v_imported_1059_; lean_object* v_ctx_1060_; lean_object* v_scopes_1061_; uint8_t v___y_1063_; uint8_t v___x_1066_; 
v_name_1054_ = lean_ctor_get(v_v_u2081_1052_, 0);
v_imported_1055_ = lean_ctor_get(v_v_u2081_1052_, 1);
v_ctx_1056_ = lean_ctor_get(v_v_u2081_1052_, 2);
v_scopes_1057_ = lean_ctor_get(v_v_u2081_1052_, 3);
v_name_1058_ = lean_ctor_get(v_v_u2082_1053_, 0);
v_imported_1059_ = lean_ctor_get(v_v_u2082_1053_, 1);
v_ctx_1060_ = lean_ctor_get(v_v_u2082_1053_, 2);
v_scopes_1061_ = lean_ctor_get(v_v_u2082_1053_, 3);
v___x_1066_ = l_Lean_Name_isSuffixOf(v_name_1054_, v_name_1058_);
if (v___x_1066_ == 0)
{
v___y_1063_ = v___x_1066_;
goto v___jp_1062_;
}
else
{
uint8_t v___x_1067_; 
v___x_1067_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1057_, v_scopes_1061_);
v___y_1063_ = v___x_1067_;
goto v___jp_1062_;
}
v___jp_1062_:
{
if (v___y_1063_ == 0)
{
return v___y_1063_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_name_eq(v_ctx_1056_, v_ctx_1060_);
if (v___x_1064_ == 0)
{
return v___x_1064_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_name_eq(v_imported_1055_, v_imported_1059_);
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object* v_v_u2081_1068_, lean_object* v_v_u2082_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_1068_, v_v_u2082_1069_);
lean_dec_ref(v_v_u2082_1069_);
lean_dec_ref(v_v_u2081_1068_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
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
