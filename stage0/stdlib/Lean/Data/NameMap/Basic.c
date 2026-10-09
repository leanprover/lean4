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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___redArg();
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNameMap___redArg();
LEAN_EXPORT lean_object* l_Lean_mkNameMap___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameMap_instInsertProdName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameMap_instInsertProdName___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_instInsertProdName___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_instInsertProdName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg();
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_NameSSet_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_NameSSet_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_NameSSet_empty;
LEAN_EXPORT lean_object* l_Lean_NameSSet_instEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_NameSSet_instInhabited;
static const lean_closure_object l_Lean_NameSSet_insert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSSet_insert___closed__0 = (const lean_object*)&l_Lean_NameSSet_insert___closed__0_value;
static const lean_closure_object l_Lean_NameSSet_insert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameSSet_insert___closed__1 = (const lean_object*)&l_Lean_NameSSet_insert___closed__1_value;
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
lean_object* l_Lean_mkNameMap___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(1);
return v___x_2_;
}
}
LEAN_EXPORT void l_Lean_mkNameMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Lean_mkNameMap___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Lean_mkNameMap___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_mkNameMap___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(1);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___lam__0(lean_object* v_x1_8_, lean_object* v_x2_9_, lean_object* v_x3_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_x1_8_);
lean_ctor_set(v___x_11_, 1, v_x2_9_);
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v_x3_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg(lean_object* v_inst_37_, lean_object* v_m_38_, lean_object* v_prec_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___f_40_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__0));
v___x_41_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__1));
v___x_42_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__3));
v___f_43_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_43_, 0, v_inst_37_);
v___x_44_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_44_, 0, lean_box(0));
lean_closure_set(v___x_44_, 1, lean_box(0));
lean_closure_set(v___x_44_, 2, v___x_41_);
lean_closure_set(v___x_44_, 3, v___f_43_);
v___x_45_ = lean_box(0);
v___x_46_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__13));
v___x_47_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_46_, v___f_40_, v___x_45_, v_m_38_);
v___x_48_ = l_List_repr___redArg(v___x_44_, v___x_47_);
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_42_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = l_Repr_addAppParen(v___x_49_, v_prec_39_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___boxed(lean_object* v_inst_51_, lean_object* v_m_52_, lean_object* v_prec_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_NameMap_instRepr___aux__1___redArg(v_inst_51_, v_m_52_, v_prec_53_);
lean_dec(v_prec_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_m_57_, lean_object* v_prec_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___f_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___f_59_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__0));
v___x_60_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__1));
v___x_61_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__3));
v___f_62_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_62_, 0, v_inst_56_);
v___x_63_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_63_, 0, lean_box(0));
lean_closure_set(v___x_63_, 1, lean_box(0));
lean_closure_set(v___x_63_, 2, v___x_60_);
lean_closure_set(v___x_63_, 3, v___f_62_);
v___x_64_ = lean_box(0);
v___x_65_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__13));
v___x_66_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_65_, v___f_59_, v___x_64_, v_m_57_);
v___x_67_ = l_List_repr___redArg(v___x_63_, v___x_66_);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_61_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = l_Repr_addAppParen(v___x_68_, v_prec_58_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___boxed(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_m_72_, lean_object* v_prec_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_NameMap_instRepr___aux__1(v_00_u03b1_70_, v_inst_71_, v_m_72_, v_prec_73_);
lean_dec(v_prec_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object* v_inst_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_closure((void*)(l_Lean_NameMap_instRepr___aux__1___boxed), 4, 2);
lean_closure_set(v___x_76_, 0, lean_box(0));
lean_closure_set(v___x_76_, 1, v_inst_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object* v_00_u03b1_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_alloc_closure((void*)(l_Lean_NameMap_instRepr___aux__1___boxed), 4, 2);
lean_closure_set(v___x_79_, 0, lean_box(0));
lean_closure_set(v___x_79_, 1, v_inst_78_);
return v___x_79_;
}
}
lean_object* l_Lean_NameMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(1);
return v___x_81_;
}
}
LEAN_EXPORT void l_Lean_NameMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_82_;
v_res_82_ = l_Lean_NameMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_NameMap_instEmptyCollection___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object* v_00_u03b1_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
}
lean_object* l_Lean_NameMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(1);
return v___x_88_;
}
}
LEAN_EXPORT void l_Lean_NameMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_89_;
v_res_89_ = l_Lean_NameMap_instInhabited___redArg();
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_NameMap_instInhabited___redArg();
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object* v_00_u03b1_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(1);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object* v_k_94_, lean_object* v_v_95_, lean_object* v_t_96_){
_start:
{
if (lean_obj_tag(v_t_96_) == 0)
{
lean_object* v_size_97_; lean_object* v_k_98_; lean_object* v_v_99_; lean_object* v_l_100_; lean_object* v_r_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_381_; 
v_size_97_ = lean_ctor_get(v_t_96_, 0);
v_k_98_ = lean_ctor_get(v_t_96_, 1);
v_v_99_ = lean_ctor_get(v_t_96_, 2);
v_l_100_ = lean_ctor_get(v_t_96_, 3);
v_r_101_ = lean_ctor_get(v_t_96_, 4);
v_isSharedCheck_381_ = !lean_is_exclusive(v_t_96_);
if (v_isSharedCheck_381_ == 0)
{
v___x_103_ = v_t_96_;
v_isShared_104_ = v_isSharedCheck_381_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_r_101_);
lean_inc(v_l_100_);
lean_inc(v_v_99_);
lean_inc(v_k_98_);
lean_inc(v_size_97_);
lean_dec(v_t_96_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_381_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
uint8_t v___x_105_; 
v___x_105_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_94_, v_k_98_);
switch(v___x_105_)
{
case 0:
{
lean_object* v_impl_106_; lean_object* v___x_107_; 
lean_dec(v_size_97_);
v_impl_106_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_94_, v_v_95_, v_l_100_);
v___x_107_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_101_) == 0)
{
lean_object* v_size_108_; lean_object* v_size_109_; lean_object* v_k_110_; lean_object* v_v_111_; lean_object* v_l_112_; lean_object* v_r_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_size_108_ = lean_ctor_get(v_r_101_, 0);
v_size_109_ = lean_ctor_get(v_impl_106_, 0);
v_k_110_ = lean_ctor_get(v_impl_106_, 1);
v_v_111_ = lean_ctor_get(v_impl_106_, 2);
v_l_112_ = lean_ctor_get(v_impl_106_, 3);
v_r_113_ = lean_ctor_get(v_impl_106_, 4);
lean_inc(v_r_113_);
v___x_114_ = lean_unsigned_to_nat(3u);
v___x_115_ = lean_nat_mul(v___x_114_, v_size_108_);
v___x_116_ = lean_nat_dec_lt(v___x_115_, v_size_109_);
lean_dec(v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v_r_113_);
v___x_117_ = lean_nat_add(v___x_107_, v_size_109_);
v___x_118_ = lean_nat_add(v___x_117_, v_size_108_);
lean_dec(v___x_117_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 3, v_impl_106_);
lean_ctor_set(v___x_103_, 0, v___x_118_);
v___x_120_ = v___x_103_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_121_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_121_, 3, v_impl_106_);
lean_ctor_set(v_reuseFailAlloc_121_, 4, v_r_101_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_187_; 
lean_inc(v_l_112_);
lean_inc(v_v_111_);
lean_inc(v_k_110_);
lean_inc(v_size_109_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_impl_106_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; lean_object* v_unused_189_; lean_object* v_unused_190_; lean_object* v_unused_191_; lean_object* v_unused_192_; 
v_unused_188_ = lean_ctor_get(v_impl_106_, 4);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_impl_106_, 3);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_impl_106_, 2);
lean_dec(v_unused_190_);
v_unused_191_ = lean_ctor_get(v_impl_106_, 1);
lean_dec(v_unused_191_);
v_unused_192_ = lean_ctor_get(v_impl_106_, 0);
lean_dec(v_unused_192_);
v___x_123_ = v_impl_106_;
v_isShared_124_ = v_isSharedCheck_187_;
goto v_resetjp_122_;
}
else
{
lean_dec(v_impl_106_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_187_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_size_125_; lean_object* v_size_126_; lean_object* v_k_127_; lean_object* v_v_128_; lean_object* v_l_129_; lean_object* v_r_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_size_125_ = lean_ctor_get(v_l_112_, 0);
v_size_126_ = lean_ctor_get(v_r_113_, 0);
v_k_127_ = lean_ctor_get(v_r_113_, 1);
v_v_128_ = lean_ctor_get(v_r_113_, 2);
v_l_129_ = lean_ctor_get(v_r_113_, 3);
v_r_130_ = lean_ctor_get(v_r_113_, 4);
v___x_131_ = lean_unsigned_to_nat(2u);
v___x_132_ = lean_nat_mul(v___x_131_, v_size_125_);
v___x_133_ = lean_nat_dec_lt(v_size_126_, v___x_132_);
lean_dec(v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_162_; 
lean_inc(v_r_130_);
lean_inc(v_l_129_);
lean_inc(v_v_128_);
lean_inc(v_k_127_);
v_isSharedCheck_162_ = !lean_is_exclusive(v_r_113_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; lean_object* v_unused_164_; lean_object* v_unused_165_; lean_object* v_unused_166_; lean_object* v_unused_167_; 
v_unused_163_ = lean_ctor_get(v_r_113_, 4);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_r_113_, 3);
lean_dec(v_unused_164_);
v_unused_165_ = lean_ctor_get(v_r_113_, 2);
lean_dec(v_unused_165_);
v_unused_166_ = lean_ctor_get(v_r_113_, 1);
lean_dec(v_unused_166_);
v_unused_167_ = lean_ctor_get(v_r_113_, 0);
lean_dec(v_unused_167_);
v___x_135_ = v_r_113_;
v_isShared_136_ = v_isSharedCheck_162_;
goto v_resetjp_134_;
}
else
{
lean_dec(v_r_113_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_162_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___y_140_; lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v___x_150_; lean_object* v___y_152_; 
v___x_137_ = lean_nat_add(v___x_107_, v_size_109_);
lean_dec(v_size_109_);
v___x_138_ = lean_nat_add(v___x_137_, v_size_108_);
lean_dec(v___x_137_);
v___x_150_ = lean_nat_add(v___x_107_, v_size_125_);
if (lean_obj_tag(v_l_129_) == 0)
{
lean_object* v_size_160_; 
v_size_160_ = lean_ctor_get(v_l_129_, 0);
lean_inc(v_size_160_);
v___y_152_ = v_size_160_;
goto v___jp_151_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___y_152_ = v___x_161_;
goto v___jp_151_;
}
v___jp_139_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_nat_add(v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec(v___y_141_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 4, v_r_101_);
lean_ctor_set(v___x_135_, 3, v_r_130_);
lean_ctor_set(v___x_135_, 2, v_v_99_);
lean_ctor_set(v___x_135_, 1, v_k_98_);
lean_ctor_set(v___x_135_, 0, v___x_143_);
v___x_145_ = v___x_135_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_143_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v_r_130_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v_r_101_);
v___x_145_ = v_reuseFailAlloc_149_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 4, v___x_145_);
lean_ctor_set(v___x_123_, 3, v___y_140_);
lean_ctor_set(v___x_123_, 2, v_v_128_);
lean_ctor_set(v___x_123_, 1, v_k_127_);
lean_ctor_set(v___x_123_, 0, v___x_138_);
v___x_147_ = v___x_123_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_128_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v___y_140_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_nat_add(v___x_150_, v___y_152_);
lean_dec(v___y_152_);
lean_dec(v___x_150_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v_l_129_);
lean_ctor_set(v___x_103_, 3, v_l_112_);
lean_ctor_set(v___x_103_, 2, v_v_111_);
lean_ctor_set(v___x_103_, 1, v_k_110_);
lean_ctor_set(v___x_103_, 0, v___x_153_);
v___x_155_ = v___x_103_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v_l_112_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v_l_129_);
v___x_155_ = v_reuseFailAlloc_159_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_nat_add(v___x_107_, v_size_108_);
if (lean_obj_tag(v_r_130_) == 0)
{
lean_object* v_size_157_; 
v_size_157_ = lean_ctor_get(v_r_130_, 0);
lean_inc(v_size_157_);
v___y_140_ = v___x_155_;
v___y_141_ = v___x_156_;
v___y_142_ = v_size_157_;
goto v___jp_139_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___y_140_ = v___x_155_;
v___y_141_ = v___x_156_;
v___y_142_ = v___x_158_;
goto v___jp_139_;
}
}
}
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
lean_del_object(v___x_103_);
v___x_168_ = lean_nat_add(v___x_107_, v_size_109_);
lean_dec(v_size_109_);
v___x_169_ = lean_nat_add(v___x_168_, v_size_108_);
lean_dec(v___x_168_);
v___x_170_ = lean_nat_add(v___x_107_, v_size_108_);
v___x_171_ = lean_nat_add(v___x_170_, v_size_126_);
lean_dec(v___x_170_);
lean_inc_ref(v_r_101_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 4, v_r_101_);
lean_ctor_set(v___x_123_, 3, v_r_113_);
lean_ctor_set(v___x_123_, 2, v_v_99_);
lean_ctor_set(v___x_123_, 1, v_k_98_);
lean_ctor_set(v___x_123_, 0, v___x_171_);
v___x_173_ = v___x_123_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_186_, 3, v_r_113_);
lean_ctor_set(v_reuseFailAlloc_186_, 4, v_r_101_);
v___x_173_ = v_reuseFailAlloc_186_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_isSharedCheck_180_ = !lean_is_exclusive(v_r_101_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; 
v_unused_181_ = lean_ctor_get(v_r_101_, 4);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_r_101_, 3);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_r_101_, 2);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_r_101_, 1);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_r_101_, 0);
lean_dec(v_unused_185_);
v___x_175_ = v_r_101_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_dec(v_r_101_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 4, v___x_173_);
lean_ctor_set(v___x_175_, 3, v_l_112_);
lean_ctor_set(v___x_175_, 2, v_v_111_);
lean_ctor_set(v___x_175_, 1, v_k_110_);
lean_ctor_set(v___x_175_, 0, v___x_169_);
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_111_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_l_112_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v___x_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_193_; 
v_l_193_ = lean_ctor_get(v_impl_106_, 3);
if (lean_obj_tag(v_l_193_) == 0)
{
lean_object* v_r_194_; lean_object* v_k_195_; lean_object* v_v_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_207_; 
lean_inc_ref(v_l_193_);
v_r_194_ = lean_ctor_get(v_impl_106_, 4);
v_k_195_ = lean_ctor_get(v_impl_106_, 1);
v_v_196_ = lean_ctor_get(v_impl_106_, 2);
v_isSharedCheck_207_ = !lean_is_exclusive(v_impl_106_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; 
v_unused_208_ = lean_ctor_get(v_impl_106_, 3);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_impl_106_, 0);
lean_dec(v_unused_209_);
v___x_198_ = v_impl_106_;
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_r_194_);
lean_inc(v_v_196_);
lean_inc(v_k_195_);
lean_dec(v_impl_106_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_194_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 3, v_r_194_);
lean_ctor_set(v___x_198_, 2, v_v_99_);
lean_ctor_set(v___x_198_, 1, v_k_98_);
lean_ctor_set(v___x_198_, 0, v___x_107_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_r_194_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_r_194_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_204_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v___x_202_);
lean_ctor_set(v___x_103_, 3, v_l_193_);
lean_ctor_set(v___x_103_, 2, v_v_196_);
lean_ctor_set(v___x_103_, 1, v_k_195_);
lean_ctor_set(v___x_103_, 0, v___x_200_);
v___x_204_ = v___x_103_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_k_195_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_v_196_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_l_193_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_r_210_; 
v_r_210_ = lean_ctor_get(v_impl_106_, 4);
lean_inc(v_r_210_);
if (lean_obj_tag(v_r_210_) == 0)
{
lean_object* v_k_211_; lean_object* v_v_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_235_; 
lean_inc(v_l_193_);
v_k_211_ = lean_ctor_get(v_impl_106_, 1);
v_v_212_ = lean_ctor_get(v_impl_106_, 2);
v_isSharedCheck_235_ = !lean_is_exclusive(v_impl_106_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_236_ = lean_ctor_get(v_impl_106_, 4);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_impl_106_, 3);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_impl_106_, 0);
lean_dec(v_unused_238_);
v___x_214_ = v_impl_106_;
v_isShared_215_ = v_isSharedCheck_235_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_v_212_);
lean_inc(v_k_211_);
lean_dec(v_impl_106_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_235_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_k_216_; lean_object* v_v_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_231_; 
v_k_216_ = lean_ctor_get(v_r_210_, 1);
v_v_217_ = lean_ctor_get(v_r_210_, 2);
v_isSharedCheck_231_ = !lean_is_exclusive(v_r_210_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; lean_object* v_unused_233_; lean_object* v_unused_234_; 
v_unused_232_ = lean_ctor_get(v_r_210_, 4);
lean_dec(v_unused_232_);
v_unused_233_ = lean_ctor_get(v_r_210_, 3);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_r_210_, 0);
lean_dec(v_unused_234_);
v___x_219_ = v_r_210_;
v_isShared_220_ = v_isSharedCheck_231_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_v_217_);
lean_inc(v_k_216_);
lean_dec(v_r_210_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_231_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = lean_unsigned_to_nat(3u);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 4, v_l_193_);
lean_ctor_set(v___x_219_, 3, v_l_193_);
lean_ctor_set(v___x_219_, 2, v_v_212_);
lean_ctor_set(v___x_219_, 1, v_k_211_);
lean_ctor_set(v___x_219_, 0, v___x_107_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_k_211_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_v_212_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_l_193_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_l_193_);
v___x_223_ = v_reuseFailAlloc_230_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_225_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 4, v_l_193_);
lean_ctor_set(v___x_214_, 2, v_v_99_);
lean_ctor_set(v___x_214_, 1, v_k_98_);
lean_ctor_set(v___x_214_, 0, v___x_107_);
v___x_225_ = v___x_214_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v_l_193_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v_l_193_);
v___x_225_ = v_reuseFailAlloc_229_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v___x_225_);
lean_ctor_set(v___x_103_, 3, v___x_223_);
lean_ctor_set(v___x_103_, 2, v_v_217_);
lean_ctor_set(v___x_103_, 1, v_k_216_);
lean_ctor_set(v___x_103_, 0, v___x_221_);
v___x_227_ = v___x_103_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_216_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_unsigned_to_nat(2u);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v_r_210_);
lean_ctor_set(v___x_103_, 3, v_impl_106_);
lean_ctor_set(v___x_103_, 0, v___x_239_);
v___x_241_ = v___x_103_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_impl_106_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_r_210_);
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
case 1:
{
lean_object* v___x_244_; 
lean_dec(v_v_99_);
lean_dec(v_k_98_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 2, v_v_95_);
lean_ctor_set(v___x_103_, 1, v_k_94_);
v___x_244_ = v___x_103_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_size_97_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_k_94_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_v_95_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v_r_101_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
default: 
{
lean_object* v_impl_246_; lean_object* v___x_247_; 
lean_dec(v_size_97_);
v_impl_246_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_94_, v_v_95_, v_r_101_);
v___x_247_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_100_) == 0)
{
lean_object* v_size_248_; lean_object* v_size_249_; lean_object* v_k_250_; lean_object* v_v_251_; lean_object* v_l_252_; lean_object* v_r_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_size_248_ = lean_ctor_get(v_l_100_, 0);
v_size_249_ = lean_ctor_get(v_impl_246_, 0);
v_k_250_ = lean_ctor_get(v_impl_246_, 1);
v_v_251_ = lean_ctor_get(v_impl_246_, 2);
v_l_252_ = lean_ctor_get(v_impl_246_, 3);
lean_inc(v_l_252_);
v_r_253_ = lean_ctor_get(v_impl_246_, 4);
v___x_254_ = lean_unsigned_to_nat(3u);
v___x_255_ = lean_nat_mul(v___x_254_, v_size_248_);
v___x_256_ = lean_nat_dec_lt(v___x_255_, v_size_249_);
lean_dec(v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec(v_l_252_);
v___x_257_ = lean_nat_add(v___x_247_, v_size_248_);
v___x_258_ = lean_nat_add(v___x_257_, v_size_249_);
lean_dec(v___x_257_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v_impl_246_);
lean_ctor_set(v___x_103_, 0, v___x_258_);
v___x_260_ = v___x_103_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_impl_246_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
else
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_325_; 
lean_inc(v_r_253_);
lean_inc(v_v_251_);
lean_inc(v_k_250_);
lean_inc(v_size_249_);
v_isSharedCheck_325_ = !lean_is_exclusive(v_impl_246_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; lean_object* v_unused_327_; lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; 
v_unused_326_ = lean_ctor_get(v_impl_246_, 4);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_impl_246_, 3);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_impl_246_, 2);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_impl_246_, 1);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_impl_246_, 0);
lean_dec(v_unused_330_);
v___x_263_ = v_impl_246_;
v_isShared_264_ = v_isSharedCheck_325_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_impl_246_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_325_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_size_265_; lean_object* v_k_266_; lean_object* v_v_267_; lean_object* v_l_268_; lean_object* v_r_269_; lean_object* v_size_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_size_265_ = lean_ctor_get(v_l_252_, 0);
v_k_266_ = lean_ctor_get(v_l_252_, 1);
v_v_267_ = lean_ctor_get(v_l_252_, 2);
v_l_268_ = lean_ctor_get(v_l_252_, 3);
v_r_269_ = lean_ctor_get(v_l_252_, 4);
v_size_270_ = lean_ctor_get(v_r_253_, 0);
v___x_271_ = lean_unsigned_to_nat(2u);
v___x_272_ = lean_nat_mul(v___x_271_, v_size_270_);
v___x_273_ = lean_nat_dec_lt(v_size_265_, v___x_272_);
lean_dec(v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_301_; 
lean_inc(v_r_269_);
lean_inc(v_l_268_);
lean_inc(v_v_267_);
lean_inc(v_k_266_);
v_isSharedCheck_301_ = !lean_is_exclusive(v_l_252_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; lean_object* v_unused_306_; 
v_unused_302_ = lean_ctor_get(v_l_252_, 4);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_l_252_, 3);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_l_252_, 2);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_l_252_, 1);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_l_252_, 0);
lean_dec(v_unused_306_);
v___x_275_ = v_l_252_;
v_isShared_276_ = v_isSharedCheck_301_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_l_252_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_301_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_291_; 
v___x_277_ = lean_nat_add(v___x_247_, v_size_248_);
v___x_278_ = lean_nat_add(v___x_277_, v_size_249_);
lean_dec(v_size_249_);
if (lean_obj_tag(v_l_268_) == 0)
{
lean_object* v_size_299_; 
v_size_299_ = lean_ctor_get(v_l_268_, 0);
lean_inc(v_size_299_);
v___y_291_ = v_size_299_;
goto v___jp_290_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___y_291_ = v___x_300_;
goto v___jp_290_;
}
v___jp_279_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_nat_add(v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec(v___y_281_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 4, v_r_253_);
lean_ctor_set(v___x_275_, 3, v_r_269_);
lean_ctor_set(v___x_275_, 2, v_v_251_);
lean_ctor_set(v___x_275_, 1, v_k_250_);
lean_ctor_set(v___x_275_, 0, v___x_283_);
v___x_285_ = v___x_275_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_k_250_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v_v_251_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v_r_269_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v_r_253_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 4, v___x_285_);
lean_ctor_set(v___x_263_, 3, v___y_280_);
lean_ctor_set(v___x_263_, 2, v_v_267_);
lean_ctor_set(v___x_263_, 1, v_k_266_);
lean_ctor_set(v___x_263_, 0, v___x_278_);
v___x_287_ = v___x_263_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_266_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_267_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v___y_280_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_nat_add(v___x_277_, v___y_291_);
lean_dec(v___y_291_);
lean_dec(v___x_277_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v_l_268_);
lean_ctor_set(v___x_103_, 0, v___x_292_);
v___x_294_ = v___x_103_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_l_268_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = lean_nat_add(v___x_247_, v_size_270_);
if (lean_obj_tag(v_r_269_) == 0)
{
lean_object* v_size_296_; 
v_size_296_ = lean_ctor_get(v_r_269_, 0);
lean_inc(v_size_296_);
v___y_280_ = v___x_294_;
v___y_281_ = v___x_295_;
v___y_282_ = v_size_296_;
goto v___jp_279_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___y_280_ = v___x_294_;
v___y_281_ = v___x_295_;
v___y_282_ = v___x_297_;
goto v___jp_279_;
}
}
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
lean_del_object(v___x_103_);
v___x_307_ = lean_nat_add(v___x_247_, v_size_248_);
v___x_308_ = lean_nat_add(v___x_307_, v_size_249_);
lean_dec(v_size_249_);
v___x_309_ = lean_nat_add(v___x_307_, v_size_265_);
lean_dec(v___x_307_);
lean_inc_ref(v_l_100_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 4, v_l_252_);
lean_ctor_set(v___x_263_, 3, v_l_100_);
lean_ctor_set(v___x_263_, 2, v_v_99_);
lean_ctor_set(v___x_263_, 1, v_k_98_);
lean_ctor_set(v___x_263_, 0, v___x_309_);
v___x_311_ = v___x_263_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_l_100_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v_l_252_);
v___x_311_ = v_reuseFailAlloc_324_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_isSharedCheck_318_ = !lean_is_exclusive(v_l_100_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; 
v_unused_319_ = lean_ctor_get(v_l_100_, 4);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_l_100_, 3);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_l_100_, 2);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_l_100_, 1);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_l_100_, 0);
lean_dec(v_unused_323_);
v___x_313_ = v_l_100_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_dec(v_l_100_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v_r_253_);
lean_ctor_set(v___x_313_, 3, v___x_311_);
lean_ctor_set(v___x_313_, 2, v_v_251_);
lean_ctor_set(v___x_313_, 1, v_k_250_);
lean_ctor_set(v___x_313_, 0, v___x_308_);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_k_250_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_v_251_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_r_253_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_331_; 
v_l_331_ = lean_ctor_get(v_impl_246_, 3);
lean_inc(v_l_331_);
if (lean_obj_tag(v_l_331_) == 0)
{
lean_object* v_r_332_; lean_object* v_k_333_; lean_object* v_v_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_357_; 
v_r_332_ = lean_ctor_get(v_impl_246_, 4);
v_k_333_ = lean_ctor_get(v_impl_246_, 1);
v_v_334_ = lean_ctor_get(v_impl_246_, 2);
v_isSharedCheck_357_ = !lean_is_exclusive(v_impl_246_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; lean_object* v_unused_359_; 
v_unused_358_ = lean_ctor_get(v_impl_246_, 3);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_impl_246_, 0);
lean_dec(v_unused_359_);
v___x_336_ = v_impl_246_;
v_isShared_337_ = v_isSharedCheck_357_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_r_332_);
lean_inc(v_v_334_);
lean_inc(v_k_333_);
lean_dec(v_impl_246_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_357_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_k_338_; lean_object* v_v_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_353_; 
v_k_338_ = lean_ctor_get(v_l_331_, 1);
v_v_339_ = lean_ctor_get(v_l_331_, 2);
v_isSharedCheck_353_ = !lean_is_exclusive(v_l_331_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_354_ = lean_ctor_get(v_l_331_, 4);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_l_331_, 3);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_l_331_, 0);
lean_dec(v_unused_356_);
v___x_341_ = v_l_331_;
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_v_339_);
lean_inc(v_k_338_);
lean_dec(v_l_331_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_332_, 2);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v_r_332_);
lean_ctor_set(v___x_341_, 3, v_r_332_);
lean_ctor_set(v___x_341_, 2, v_v_99_);
lean_ctor_set(v___x_341_, 1, v_k_98_);
lean_ctor_set(v___x_341_, 0, v___x_247_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_r_332_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_r_332_);
v___x_345_ = v_reuseFailAlloc_352_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_347_; 
lean_inc(v_r_332_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 3, v_r_332_);
lean_ctor_set(v___x_336_, 0, v___x_247_);
v___x_347_ = v___x_336_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_k_333_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_v_334_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_r_332_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_r_332_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_349_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v___x_347_);
lean_ctor_set(v___x_103_, 3, v___x_345_);
lean_ctor_set(v___x_103_, 2, v_v_339_);
lean_ctor_set(v___x_103_, 1, v_k_338_);
lean_ctor_set(v___x_103_, 0, v___x_343_);
v___x_349_ = v___x_103_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_338_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_339_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
else
{
lean_object* v_r_360_; 
v_r_360_ = lean_ctor_get(v_impl_246_, 4);
lean_inc(v_r_360_);
if (lean_obj_tag(v_r_360_) == 0)
{
lean_object* v_k_361_; lean_object* v_v_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_373_; 
v_k_361_ = lean_ctor_get(v_impl_246_, 1);
v_v_362_ = lean_ctor_get(v_impl_246_, 2);
v_isSharedCheck_373_ = !lean_is_exclusive(v_impl_246_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_374_ = lean_ctor_get(v_impl_246_, 4);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_impl_246_, 3);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_impl_246_, 0);
lean_dec(v_unused_376_);
v___x_364_ = v_impl_246_;
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_v_362_);
lean_inc(v_k_361_);
lean_dec(v_impl_246_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(3u);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 4, v_l_331_);
lean_ctor_set(v___x_364_, 2, v_v_99_);
lean_ctor_set(v___x_364_, 1, v_k_98_);
lean_ctor_set(v___x_364_, 0, v___x_247_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_l_331_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_l_331_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v_r_360_);
lean_ctor_set(v___x_103_, 3, v___x_368_);
lean_ctor_set(v___x_103_, 2, v_v_362_);
lean_ctor_set(v___x_103_, 1, v_k_361_);
lean_ctor_set(v___x_103_, 0, v___x_366_);
v___x_370_ = v___x_103_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_k_361_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_v_362_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_r_360_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_unsigned_to_nat(2u);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 4, v_impl_246_);
lean_ctor_set(v___x_103_, 3, v_r_360_);
lean_ctor_set(v___x_103_, 0, v___x_377_);
v___x_379_ = v___x_103_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_k_98_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_v_99_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v_r_360_);
lean_ctor_set(v_reuseFailAlloc_380_, 4, v_impl_246_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
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
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_k_94_);
lean_ctor_set(v___x_383_, 2, v_v_95_);
lean_ctor_set(v___x_383_, 3, v_t_96_);
lean_ctor_set(v___x_383_, 4, v_t_96_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object* v_m_384_, lean_object* v_n_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_385_, v_a_386_, v_m_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object* v_00_u03b1_388_, lean_object* v_m_389_, lean_object* v_n_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_390_, v_a_391_, v_m_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0(lean_object* v_00_u03b2_393_, lean_object* v_k_394_, lean_object* v_v_395_, lean_object* v_t_396_, lean_object* v_hl_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_394_, v_v_395_, v_t_396_);
return v___x_398_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object* v_k_399_, lean_object* v_t_400_){
_start:
{
if (lean_obj_tag(v_t_400_) == 0)
{
lean_object* v_k_401_; lean_object* v_l_402_; lean_object* v_r_403_; uint8_t v___x_404_; 
v_k_401_ = lean_ctor_get(v_t_400_, 1);
v_l_402_ = lean_ctor_get(v_t_400_, 3);
v_r_403_ = lean_ctor_get(v_t_400_, 4);
v___x_404_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_399_, v_k_401_);
switch(v___x_404_)
{
case 0:
{
v_t_400_ = v_l_402_;
goto _start;
}
case 1:
{
uint8_t v___x_406_; 
v___x_406_ = 1;
return v___x_406_;
}
default: 
{
v_t_400_ = v_r_403_;
goto _start;
}
}
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 0;
return v___x_408_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_399_ = stack[0].m_obj;
lean_object* v_t_400_ = stack[1].m_obj;
uint8_t v_res_409_;
v_res_409_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_399_, v_t_400_);
stack->m_num = v_res_409_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg___boxed(lean_object* v_k_410_, lean_object* v_t_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_410_, v_t_411_);
lean_dec(v_t_411_);
lean_dec(v_k_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
uint8_t l_Lean_NameMap_contains___redArg(lean_object* v_m_414_, lean_object* v_n_415_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_415_, v_m_414_);
return v___x_416_;
}
}
LEAN_EXPORT void l_Lean_NameMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_414_ = stack[0].m_obj;
lean_object* v_n_415_ = stack[1].m_obj;
uint8_t v_res_417_;
v_res_417_ = l_Lean_NameMap_contains___redArg(v_m_414_, v_n_415_);
stack->m_num = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object* v_m_418_, lean_object* v_n_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lean_NameMap_contains___redArg(v_m_418_, v_n_419_);
lean_dec(v_n_419_);
lean_dec(v_m_418_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
uint8_t l_Lean_NameMap_contains(lean_object* v_00_u03b1_422_, lean_object* v_m_423_, lean_object* v_n_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_424_, v_m_423_);
return v___x_425_;
}
}
LEAN_EXPORT void l_Lean_NameMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_423_ = stack[1].m_obj;
lean_object* v_n_424_ = stack[2].m_obj;
uint8_t v_res_426_;
v_res_426_ = l_Lean_NameMap_contains(lean_box(0), v_m_423_, v_n_424_);
stack->m_num = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object* v_00_u03b1_427_, lean_object* v_m_428_, lean_object* v_n_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_Lean_NameMap_contains(v_00_u03b1_427_, v_m_428_, v_n_429_);
lean_dec(v_n_429_);
lean_dec(v_m_428_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(lean_object* v_00_u03b2_432_, lean_object* v_k_433_, lean_object* v_t_434_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_433_, v_t_434_);
return v___x_435_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_433_ = stack[1].m_obj;
lean_object* v_t_434_ = stack[2].m_obj;
uint8_t v_res_436_;
v_res_436_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(lean_box(0), v_k_433_, v_t_434_);
stack->m_num = v_res_436_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___boxed(lean_object* v_00_u03b2_437_, lean_object* v_k_438_, lean_object* v_t_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(v_00_u03b2_437_, v_k_438_, v_t_439_);
lean_dec(v_t_439_);
lean_dec(v_k_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object* v_t_442_, lean_object* v_k_443_){
_start:
{
if (lean_obj_tag(v_t_442_) == 0)
{
lean_object* v_k_444_; lean_object* v_v_445_; lean_object* v_l_446_; lean_object* v_r_447_; uint8_t v___x_448_; 
v_k_444_ = lean_ctor_get(v_t_442_, 1);
v_v_445_ = lean_ctor_get(v_t_442_, 2);
v_l_446_ = lean_ctor_get(v_t_442_, 3);
v_r_447_ = lean_ctor_get(v_t_442_, 4);
v___x_448_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_443_, v_k_444_);
switch(v___x_448_)
{
case 0:
{
v_t_442_ = v_l_446_;
goto _start;
}
case 1:
{
lean_object* v___x_450_; 
lean_inc(v_v_445_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_v_445_);
return v___x_450_;
}
default: 
{
v_t_442_ = v_r_447_;
goto _start;
}
}
}
else
{
lean_object* v___x_452_; 
v___x_452_ = lean_box(0);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg___boxed(lean_object* v_t_453_, lean_object* v_k_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_453_, v_k_454_);
lean_dec(v_k_454_);
lean_dec(v_t_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object* v_m_456_, lean_object* v_n_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_456_, v_n_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object* v_m_459_, lean_object* v_n_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_NameMap_find_x3f___redArg(v_m_459_, v_n_460_);
lean_dec(v_n_460_);
lean_dec(v_m_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object* v_00_u03b1_462_, lean_object* v_m_463_, lean_object* v_n_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_463_, v_n_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object* v_00_u03b1_466_, lean_object* v_m_467_, lean_object* v_n_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_NameMap_find_x3f(v_00_u03b1_466_, v_m_467_, v_n_468_);
lean_dec(v_n_468_);
lean_dec(v_m_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(lean_object* v_00_u03b4_470_, lean_object* v_t_471_, lean_object* v_k_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_471_, v_k_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b4_474_, lean_object* v_t_475_, lean_object* v_k_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(v_00_u03b4_474_, v_t_475_, v_k_476_);
lean_dec(v_k_476_);
lean_dec(v_t_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg___lam__0(lean_object* v_e_478_, lean_object* v_s_479_){
_start:
{
lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_482_; 
v_fst_480_ = lean_ctor_get(v_e_478_, 0);
lean_inc(v_fst_480_);
v_snd_481_ = lean_ctor_get(v_e_478_, 1);
lean_inc(v_snd_481_);
lean_dec_ref(v_e_478_);
v___x_482_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_480_, v_snd_481_, v_s_479_);
return v___x_482_;
}
}
lean_object* l_Lean_NameMap_instInsertProdName___redArg(){
_start:
{
lean_object* v___f_485_; 
v___f_485_ = ((lean_object*)(l_Lean_NameMap_instInsertProdName___redArg___closed__0));
return v___f_485_;
}
}
LEAN_EXPORT void l_Lean_NameMap_instInsertProdName___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_486_;
v_res_486_ = l_Lean_NameMap_instInsertProdName___redArg();
stack->m_obj
 = v_res_486_;
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg___boxed(lean_object* v___dummy_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_NameMap_instInsertProdName___redArg();
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName(lean_object* v_00_u03b1_489_){
_start:
{
lean_object* v___f_490_; 
v___f_490_ = ((lean_object*)(l_Lean_NameMap_instInsertProdName___redArg___closed__0));
return v___f_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_491_, lean_object* v_a_492_, lean_object* v_b_493_, lean_object* v_c_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_a_492_);
lean_ctor_set(v___x_495_, 1, v_b_493_);
v___x_496_ = lean_apply_2(v_f_491_, v___x_495_, v_c_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_497_, lean_object* v_____do__lift_498_){
_start:
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_ctor_get(v_____do__lift_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v_____do__lift_498_);
v___x_500_ = lean_apply_2(v_toPure_497_, lean_box(0), v_a_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg(lean_object* v_inst_501_, lean_object* v_m_502_, lean_object* v_init_503_, lean_object* v_f_504_){
_start:
{
lean_object* v_toApplicative_505_; lean_object* v_toBind_506_; lean_object* v_toPure_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___f_510_; lean_object* v___x_511_; 
v_toApplicative_505_ = lean_ctor_get(v_inst_501_, 0);
v_toBind_506_ = lean_ctor_get(v_inst_501_, 1);
lean_inc(v_toBind_506_);
v_toPure_507_ = lean_ctor_get(v_toApplicative_505_, 1);
lean_inc(v_toPure_507_);
v___f_508_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_508_, 0, v_f_504_);
v___x_509_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_501_, v___f_508_, v_init_503_, v_m_502_);
v___f_510_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_510_, 0, v_toPure_507_);
v___x_511_ = lean_apply_4(v_toBind_506_, lean_box(0), lean_box(0), v___x_509_, v___f_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1(lean_object* v_00_u03b1_512_, lean_object* v_m_513_, lean_object* v_inst_514_, lean_object* v_00_u03b2_515_, lean_object* v_m_516_, lean_object* v_init_517_, lean_object* v_f_518_){
_start:
{
lean_object* v_toApplicative_519_; lean_object* v_toBind_520_; lean_object* v_toPure_521_; lean_object* v___f_522_; lean_object* v___x_523_; lean_object* v___f_524_; lean_object* v___x_525_; 
v_toApplicative_519_ = lean_ctor_get(v_inst_514_, 0);
v_toBind_520_ = lean_ctor_get(v_inst_514_, 1);
lean_inc(v_toBind_520_);
v_toPure_521_ = lean_ctor_get(v_toApplicative_519_, 1);
lean_inc(v_toPure_521_);
v___f_522_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_522_, 0, v_f_518_);
v___x_523_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_514_, v___f_522_, v_init_517_, v_m_516_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_524_, 0, v_toPure_521_);
v___x_525_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_523_, v___f_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___redArg(lean_object* v_inst_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_527_, 0, lean_box(0));
lean_closure_set(v___x_527_, 1, lean_box(0));
lean_closure_set(v___x_527_, 2, v_inst_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad(lean_object* v_00_u03b1_528_, lean_object* v_m_529_, lean_object* v_inst_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_531_, 0, lean_box(0));
lean_closure_set(v___x_531_, 1, lean_box(0));
lean_closure_set(v___x_531_, 2, v_inst_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object* v_f_532_, lean_object* v_t_533_){
_start:
{
if (lean_obj_tag(v_t_533_) == 0)
{
lean_object* v_k_534_; lean_object* v_v_535_; lean_object* v_l_536_; lean_object* v_r_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_k_534_ = lean_ctor_get(v_t_533_, 1);
lean_inc_n(v_k_534_, 2);
v_v_535_ = lean_ctor_get(v_t_533_, 2);
lean_inc_n(v_v_535_, 2);
v_l_536_ = lean_ctor_get(v_t_533_, 3);
lean_inc(v_l_536_);
v_r_537_ = lean_ctor_get(v_t_533_, 4);
lean_inc(v_r_537_);
lean_dec_ref_known(v_t_533_, 5);
lean_inc_ref(v_f_532_);
v___x_538_ = lean_apply_2(v_f_532_, v_k_534_, v_v_535_);
v___x_539_ = lean_unbox(v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v_impl_540_; lean_object* v_impl_541_; lean_object* v___x_542_; 
lean_dec(v_v_535_);
lean_dec(v_k_534_);
lean_inc_ref(v_f_532_);
v_impl_540_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_532_, v_l_536_);
v_impl_541_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_532_, v_r_537_);
v___x_542_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_540_, v_impl_541_);
return v___x_542_;
}
else
{
lean_object* v_impl_543_; lean_object* v_impl_544_; lean_object* v___x_545_; 
lean_inc_ref(v_f_532_);
v_impl_543_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_532_, v_l_536_);
v_impl_544_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_532_, v_r_537_);
v___x_545_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_534_, v_v_535_, v_impl_543_, v_impl_544_);
return v___x_545_;
}
}
else
{
lean_dec_ref(v_f_532_);
return v_t_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object* v_f_546_, lean_object* v_m_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_546_, v_m_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object* v_00_u03b1_549_, lean_object* v_f_550_, lean_object* v_m_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_550_, v_m_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(lean_object* v_00_u03b1_553_, lean_object* v_f_554_, lean_object* v_t_555_, lean_object* v_hl_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_554_, v_t_555_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_NameSet_empty(void){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(1);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_NameSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_box(1);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_NameSet_instInhabited(void){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_box(1);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object* v_s_561_, lean_object* v_n_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_562_, v_s_561_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(0);
v___x_565_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_562_, v___x_564_, v_s_561_);
return v___x_565_;
}
else
{
lean_dec(v_n_562_);
return v_s_561_;
}
}
}
uint8_t l_Lean_NameSet_contains(lean_object* v_s_566_, lean_object* v_n_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_567_, v_s_566_);
return v___x_568_;
}
}
LEAN_EXPORT void l_Lean_NameSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_566_ = stack[0].m_obj;
lean_object* v_n_567_ = stack[1].m_obj;
uint8_t v_res_569_;
v_res_569_ = l_Lean_NameSet_contains(v_s_566_, v_n_567_);
stack->m_num = v_res_569_;
}
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object* v_s_570_, lean_object* v_n_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lean_NameSet_contains(v_s_570_, v_n_571_);
lean_dec(v_n_571_);
lean_dec(v_s_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInsertName___lam__0(lean_object* v_n_574_, lean_object* v_s_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_NameSet_insert(v_s_575_, v_n_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_579_, lean_object* v_a_580_, lean_object* v_b_581_, lean_object* v_c_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_apply_2(v_f_579_, v_a_580_, v_c_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg(lean_object* v_inst_584_, lean_object* v_m_585_, lean_object* v_init_586_, lean_object* v_f_587_){
_start:
{
lean_object* v_toApplicative_588_; lean_object* v_toBind_589_; lean_object* v_toPure_590_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___x_594_; 
v_toApplicative_588_ = lean_ctor_get(v_inst_584_, 0);
v_toBind_589_ = lean_ctor_get(v_inst_584_, 1);
lean_inc(v_toBind_589_);
v_toPure_590_ = lean_ctor_get(v_toApplicative_588_, 1);
lean_inc(v_toPure_590_);
v___f_591_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_591_, 0, v_f_587_);
v___x_592_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_584_, v___f_591_, v_init_586_, v_m_585_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_593_, 0, v_toPure_590_);
v___x_594_ = lean_apply_4(v_toBind_589_, lean_box(0), lean_box(0), v___x_592_, v___f_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1(lean_object* v_m_595_, lean_object* v_inst_596_, lean_object* v_00_u03b2_597_, lean_object* v_m_598_, lean_object* v_init_599_, lean_object* v_f_600_){
_start:
{
lean_object* v_toApplicative_601_; lean_object* v_toBind_602_; lean_object* v_toPure_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___x_607_; 
v_toApplicative_601_ = lean_ctor_get(v_inst_596_, 0);
v_toBind_602_ = lean_ctor_get(v_inst_596_, 1);
lean_inc(v_toBind_602_);
v_toPure_603_ = lean_ctor_get(v_toApplicative_601_, 1);
lean_inc(v_toPure_603_);
v___f_604_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_604_, 0, v_f_600_);
v___x_605_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_596_, v___f_604_, v_init_599_, v_m_598_);
v___f_606_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_606_, 0, v_toPure_603_);
v___x_607_ = lean_apply_4(v_toBind_602_, lean_box(0), lean_box(0), v___x_605_, v___f_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___redArg(lean_object* v_inst_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_609_, 0, lean_box(0));
lean_closure_set(v___x_609_, 1, v_inst_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad(lean_object* v_m_610_, lean_object* v_inst_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_612_, 0, lean_box(0));
lean_closure_set(v___x_612_, 1, v_inst_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_615_, lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_b_u2082_615_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0));
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_619_, lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_619_, v_x_620_);
lean_dec(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(lean_object* v_b_u2082_622_, lean_object* v_k_623_, lean_object* v_t_624_){
_start:
{
if (lean_obj_tag(v_t_624_) == 0)
{
lean_object* v_size_625_; lean_object* v_k_626_; lean_object* v_v_627_; lean_object* v_l_628_; lean_object* v_r_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_644_; 
v_size_625_ = lean_ctor_get(v_t_624_, 0);
v_k_626_ = lean_ctor_get(v_t_624_, 1);
v_v_627_ = lean_ctor_get(v_t_624_, 2);
v_l_628_ = lean_ctor_get(v_t_624_, 3);
v_r_629_ = lean_ctor_get(v_t_624_, 4);
v_isSharedCheck_644_ = !lean_is_exclusive(v_t_624_);
if (v_isSharedCheck_644_ == 0)
{
v___x_631_ = v_t_624_;
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_r_629_);
lean_inc(v_l_628_);
lean_inc(v_v_627_);
lean_inc(v_k_626_);
lean_inc(v_size_625_);
lean_dec(v_t_624_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_644_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
uint8_t v___x_633_; 
v___x_633_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_623_, v_k_626_);
switch(v___x_633_)
{
case 0:
{
lean_object* v_impl_634_; lean_object* v___x_635_; 
lean_del_object(v___x_631_);
lean_dec(v_size_625_);
v_impl_634_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_622_, v_k_623_, v_l_628_);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_626_, v_v_627_, v_impl_634_, v_r_629_);
return v___x_635_;
}
case 1:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_val_638_; lean_object* v___x_640_; 
lean_dec(v_k_626_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v_v_627_);
v___x_637_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_622_, v___x_636_);
lean_dec_ref_known(v___x_636_, 1);
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec(v___x_637_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 2, v_val_638_);
lean_ctor_set(v___x_631_, 1, v_k_623_);
v___x_640_ = v___x_631_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_size_625_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_623_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_val_638_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_l_628_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v_r_629_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
default: 
{
lean_object* v_impl_642_; lean_object* v___x_643_; 
lean_del_object(v___x_631_);
lean_dec(v_size_625_);
v_impl_642_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_622_, v_k_623_, v_r_629_);
v___x_643_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_626_, v_v_627_, v_l_628_, v_impl_642_);
return v___x_643_;
}
}
}
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v_val_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_645_ = lean_box(0);
v___x_646_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_622_, v___x_645_);
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec(v___x_646_);
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_k_623_);
lean_ctor_set(v___x_649_, 2, v_val_647_);
lean_ctor_set(v___x_649_, 3, v_t_624_);
lean_ctor_set(v___x_649_, 4, v_t_624_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(lean_object* v_init_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v_k_652_; lean_object* v_v_653_; lean_object* v_l_654_; lean_object* v_r_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_k_652_ = lean_ctor_get(v_x_651_, 1);
lean_inc(v_k_652_);
v_v_653_ = lean_ctor_get(v_x_651_, 2);
lean_inc(v_v_653_);
v_l_654_ = lean_ctor_get(v_x_651_, 3);
lean_inc(v_l_654_);
v_r_655_ = lean_ctor_get(v_x_651_, 4);
lean_inc(v_r_655_);
lean_dec_ref_known(v_x_651_, 5);
v___x_656_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_650_, v_l_654_);
v___x_657_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_v_653_, v_k_652_, v___x_656_);
v_init_650_ = v___x_657_;
v_x_651_ = v_r_655_;
goto _start;
}
else
{
return v_init_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object* v_s_659_, lean_object* v_t_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_s_659_, v_t_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(lean_object* v_b_u2082_662_, lean_object* v_k_663_, lean_object* v_t_664_, lean_object* v_hl_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_662_, v_k_663_, v_t_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(lean_object* v_init_667_, lean_object* v_t_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_667_, v_t_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSingletonName___lam__0(lean_object* v_n_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_box(1);
v___x_674_ = l_Lean_NameSet_insert(v___x_673_, v_n_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0(lean_object* v_t_678_, lean_object* v_c_679_, lean_object* v_a_680_, lean_object* v_x_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_a_680_, v_t_678_);
if (v___x_682_ == 0)
{
lean_dec(v_a_680_);
return v_c_679_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_NameSet_insert(v_c_679_, v_a_680_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0___boxed(lean_object* v_t_684_, lean_object* v_c_685_, lean_object* v_a_686_, lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_NameSet_instInter___lam__0(v_t_684_, v_c_685_, v_a_686_, v_x_687_);
lean_dec(v_t_684_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__1(lean_object* v_s_689_, lean_object* v_t_690_){
_start:
{
lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___f_691_ = lean_alloc_closure((void*)(l_Lean_NameSet_instInter___lam__0___boxed), 4, 1);
lean_closure_set(v___f_691_, 0, v_t_690_);
v___x_692_ = lean_box(1);
v___x_693_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_691_, v___x_692_, v_s_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__0(lean_object* v___x_696_, lean_object* v_c_697_, lean_object* v_a_698_, lean_object* v_x_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_696_, v_a_698_, v_c_697_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__1(lean_object* v_s_704_, lean_object* v_t_705_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_707_; 
v___f_706_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__1));
v___x_707_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_706_, v_s_704_, v_t_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(lean_object* v_f_710_, lean_object* v_t_711_){
_start:
{
if (lean_obj_tag(v_t_711_) == 0)
{
lean_object* v_k_712_; lean_object* v_v_713_; lean_object* v_l_714_; lean_object* v_r_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_k_712_ = lean_ctor_get(v_t_711_, 1);
lean_inc_n(v_k_712_, 2);
v_v_713_ = lean_ctor_get(v_t_711_, 2);
lean_inc(v_v_713_);
v_l_714_ = lean_ctor_get(v_t_711_, 3);
lean_inc(v_l_714_);
v_r_715_ = lean_ctor_get(v_t_711_, 4);
lean_inc(v_r_715_);
lean_dec_ref_known(v_t_711_, 5);
lean_inc_ref(v_f_710_);
v___x_716_ = lean_apply_1(v_f_710_, v_k_712_);
v___x_717_ = lean_unbox(v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v_impl_718_; lean_object* v_impl_719_; lean_object* v___x_720_; 
lean_dec(v_v_713_);
lean_dec(v_k_712_);
lean_inc_ref(v_f_710_);
v_impl_718_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_710_, v_l_714_);
v_impl_719_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_710_, v_r_715_);
v___x_720_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_718_, v_impl_719_);
return v___x_720_;
}
else
{
lean_object* v_impl_721_; lean_object* v_impl_722_; lean_object* v___x_723_; 
lean_inc_ref(v_f_710_);
v_impl_721_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_710_, v_l_714_);
v_impl_722_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_710_, v_r_715_);
v___x_723_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_712_, v_v_713_, v_impl_721_, v_impl_722_);
return v___x_723_;
}
}
else
{
lean_dec_ref(v_f_710_);
return v_t_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object* v_f_724_, lean_object* v_s_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_724_, v_s_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(lean_object* v_f_727_, lean_object* v_t_728_, lean_object* v_hl_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_727_, v_t_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList(lean_object* v_l_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_733_ = l_Std_TreeSet_ofList___redArg(v_l_731_, v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList___boxed(lean_object* v_l_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_NameSet_ofList(v_l_734_);
lean_dec(v_l_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray(lean_object* v_l_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_738_ = l_Std_TreeSet_ofArray___redArg(v_l_736_, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray___boxed(lean_object* v_l_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_NameSet_ofArray(v_l_739_);
lean_dec_ref(v_l_739_);
return v_res_740_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__0(void){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_SMap_empty___redArg();
return v___x_741_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__0, &l_Lean_NameSSet_empty___closed__0_once, _init_l_Lean_NameSSet_empty___closed__0);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_NameSSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__0, &l_Lean_NameSSet_empty___closed__0_once, _init_l_Lean_NameSSet_empty___closed__0);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_NameSSet_instInhabited(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__0, &l_Lean_NameSSet_empty___closed__0_once, _init_l_Lean_NameSSet_empty___closed__0);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object* v_s_747_, lean_object* v_n_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__0));
v___x_750_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__1));
v___x_751_ = lean_box(0);
v___x_752_ = l_Lean_SMap_insert___redArg(v___x_749_, v___x_750_, v_s_747_, v_n_748_, v___x_751_);
return v___x_752_;
}
}
uint8_t l_Lean_NameSSet_contains(lean_object* v_s_753_, lean_object* v_n_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_755_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__0));
v___x_756_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__1));
v___x_757_ = l_Lean_SMap_contains___redArg(v___x_755_, v___x_756_, v_s_753_, v_n_754_);
return v___x_757_;
}
}
LEAN_EXPORT void l_Lean_NameSSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_753_ = stack[0].m_obj;
lean_object* v_n_754_ = stack[1].m_obj;
uint8_t v_res_758_;
v_res_758_ = l_Lean_NameSSet_contains(v_s_753_, v_n_754_);
stack->m_num = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object* v_s_759_, lean_object* v_n_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Lean_NameSSet_contains(v_s_759_, v_n_760_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__0(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_box(0);
v___x_764_ = lean_unsigned_to_nat(16u);
v___x_765_ = lean_mk_array(v___x_764_, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__0, &l_Lean_NameHashSet_empty___closed__0_once, _init_l_Lean_NameHashSet_empty___closed__0);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty(void){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instInhabited(void){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_771_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object* v_a_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
else
{
lean_object* v_key_775_; lean_object* v_tail_776_; uint8_t v___x_777_; 
v_key_775_ = lean_ctor_get(v_x_773_, 0);
v_tail_776_ = lean_ctor_get(v_x_773_, 2);
v___x_777_ = lean_name_eq(v_key_775_, v_a_772_);
if (v___x_777_ == 0)
{
v_x_773_ = v_tail_776_;
goto _start;
}
else
{
return v___x_777_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_772_ = stack[0].m_obj;
lean_object* v_x_773_ = stack[1].m_obj;
uint8_t v_res_779_;
v_res_779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_772_, v_x_773_);
stack->m_num = v_res_779_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_780_, lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_780_, v_x_781_);
lean_dec(v_x_781_);
lean_dec(v_a_780_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
return v_x_784_;
}
else
{
lean_object* v_key_786_; lean_object* v_value_787_; lean_object* v_tail_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_814_; 
v_key_786_ = lean_ctor_get(v_x_785_, 0);
v_value_787_ = lean_ctor_get(v_x_785_, 1);
v_tail_788_ = lean_ctor_get(v_x_785_, 2);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_785_);
if (v_isSharedCheck_814_ == 0)
{
v___x_790_ = v_x_785_;
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_tail_788_);
lean_inc(v_value_787_);
lean_inc(v_key_786_);
lean_dec(v_x_785_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_814_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; uint64_t v___y_794_; 
v___x_792_ = lean_array_get_size(v_x_784_);
if (lean_obj_tag(v_key_786_) == 0)
{
uint64_t v___x_812_; 
v___x_812_ = 1723ULL;
v___y_794_ = v___x_812_;
goto v___jp_793_;
}
else
{
uint64_t v_hash_813_; 
v_hash_813_ = lean_ctor_get_uint64(v_key_786_, sizeof(void*)*2);
v___y_794_ = v_hash_813_;
goto v___jp_793_;
}
v___jp_793_:
{
uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v_fold_797_; uint64_t v___x_798_; uint64_t v___x_799_; uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_795_ = 32ULL;
v___x_796_ = lean_uint64_shift_right(v___y_794_, v___x_795_);
v_fold_797_ = lean_uint64_xor(v___y_794_, v___x_796_);
v___x_798_ = 16ULL;
v___x_799_ = lean_uint64_shift_right(v_fold_797_, v___x_798_);
v___x_800_ = lean_uint64_xor(v_fold_797_, v___x_799_);
v___x_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = lean_usize_of_nat(v___x_792_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_sub(v___x_802_, v___x_803_);
v___x_805_ = lean_usize_land(v___x_801_, v___x_804_);
v___x_806_ = lean_array_uget_borrowed(v_x_784_, v___x_805_);
lean_inc(v___x_806_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 2, v___x_806_);
v___x_808_ = v___x_790_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_key_786_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_value_787_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v___x_806_);
v___x_808_ = v_reuseFailAlloc_811_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; 
v___x_809_ = lean_array_uset(v_x_784_, v___x_805_, v___x_808_);
v_x_784_ = v___x_809_;
v_x_785_ = v_tail_788_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_815_, lean_object* v_source_816_, lean_object* v_target_817_){
_start:
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_array_get_size(v_source_816_);
v___x_819_ = lean_nat_dec_lt(v_i_815_, v___x_818_);
if (v___x_819_ == 0)
{
lean_dec_ref(v_source_816_);
lean_dec(v_i_815_);
return v_target_817_;
}
else
{
lean_object* v_es_820_; lean_object* v___x_821_; lean_object* v_source_822_; lean_object* v_target_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_es_820_ = lean_array_fget(v_source_816_, v_i_815_);
v___x_821_ = lean_box(0);
v_source_822_ = lean_array_fset(v_source_816_, v_i_815_, v___x_821_);
v_target_823_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_817_, v_es_820_);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_i_815_, v___x_824_);
lean_dec(v_i_815_);
v_i_815_ = v___x_825_;
v_source_816_ = v_source_822_;
v_target_817_ = v_target_823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(lean_object* v_data_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_nbuckets_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_828_ = lean_array_get_size(v_data_827_);
v___x_829_ = lean_unsigned_to_nat(2u);
v_nbuckets_830_ = lean_nat_mul(v___x_828_, v___x_829_);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_box(0);
v___x_833_ = lean_mk_array(v_nbuckets_830_, v___x_832_);
v___x_834_ = lean_array_propagate_mark(v_data_827_, v___x_833_);
v___x_835_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v___x_831_, v_data_827_, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object* v_m_836_, lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
lean_object* v_size_839_; lean_object* v_buckets_840_; lean_object* v___x_841_; uint64_t v___y_843_; 
v_size_839_ = lean_ctor_get(v_m_836_, 0);
v_buckets_840_ = lean_ctor_get(v_m_836_, 1);
v___x_841_ = lean_array_get_size(v_buckets_840_);
if (lean_obj_tag(v_a_837_) == 0)
{
uint64_t v___x_880_; 
v___x_880_ = 1723ULL;
v___y_843_ = v___x_880_;
goto v___jp_842_;
}
else
{
uint64_t v_hash_881_; 
v_hash_881_ = lean_ctor_get_uint64(v_a_837_, sizeof(void*)*2);
v___y_843_ = v_hash_881_;
goto v___jp_842_;
}
v___jp_842_:
{
uint64_t v___x_844_; uint64_t v___x_845_; uint64_t v_fold_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; lean_object* v_bkt_855_; uint8_t v___x_856_; 
v___x_844_ = 32ULL;
v___x_845_ = lean_uint64_shift_right(v___y_843_, v___x_844_);
v_fold_846_ = lean_uint64_xor(v___y_843_, v___x_845_);
v___x_847_ = 16ULL;
v___x_848_ = lean_uint64_shift_right(v_fold_846_, v___x_847_);
v___x_849_ = lean_uint64_xor(v_fold_846_, v___x_848_);
v___x_850_ = lean_uint64_to_usize(v___x_849_);
v___x_851_ = lean_usize_of_nat(v___x_841_);
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_sub(v___x_851_, v___x_852_);
v___x_854_ = lean_usize_land(v___x_850_, v___x_853_);
v_bkt_855_ = lean_array_uget_borrowed(v_buckets_840_, v___x_854_);
v___x_856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_837_, v_bkt_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_877_; 
lean_inc_ref(v_buckets_840_);
lean_inc(v_size_839_);
v_isSharedCheck_877_ = !lean_is_exclusive(v_m_836_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; lean_object* v_unused_879_; 
v_unused_878_ = lean_ctor_get(v_m_836_, 1);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_m_836_, 0);
lean_dec(v_unused_879_);
v___x_858_ = v_m_836_;
v_isShared_859_ = v_isSharedCheck_877_;
goto v_resetjp_857_;
}
else
{
lean_dec(v_m_836_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_877_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v_size_x27_861_; lean_object* v___x_862_; lean_object* v_buckets_x27_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_860_ = lean_unsigned_to_nat(1u);
v_size_x27_861_ = lean_nat_add(v_size_839_, v___x_860_);
lean_dec(v_size_839_);
lean_inc(v_bkt_855_);
v___x_862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_862_, 0, v_a_837_);
lean_ctor_set(v___x_862_, 1, v_b_838_);
lean_ctor_set(v___x_862_, 2, v_bkt_855_);
v_buckets_x27_863_ = lean_array_uset(v_buckets_840_, v___x_854_, v___x_862_);
v___x_864_ = lean_unsigned_to_nat(4u);
v___x_865_ = lean_nat_mul(v_size_x27_861_, v___x_864_);
v___x_866_ = lean_unsigned_to_nat(3u);
v___x_867_ = lean_nat_div(v___x_865_, v___x_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_array_get_size(v_buckets_x27_863_);
v___x_869_ = lean_nat_dec_le(v___x_867_, v___x_868_);
lean_dec(v___x_867_);
if (v___x_869_ == 0)
{
lean_object* v_val_870_; lean_object* v___x_872_; 
v_val_870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_buckets_x27_863_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_val_870_);
lean_ctor_set(v___x_858_, 0, v_size_x27_861_);
v___x_872_ = v___x_858_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_size_x27_861_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_val_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
else
{
lean_object* v___x_875_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_buckets_x27_863_);
lean_ctor_set(v___x_858_, 0, v_size_x27_861_);
v___x_875_ = v___x_858_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_size_x27_861_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_buckets_x27_863_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_dec(v_b_838_);
lean_dec(v_a_837_);
return v_m_836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object* v_s_882_, lean_object* v_n_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_box(0);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_s_882_, v_n_883_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(lean_object* v_00_u03b2_886_, lean_object* v_m_887_, lean_object* v_a_888_, lean_object* v_b_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_887_, v_a_888_, v_b_889_);
return v___x_890_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_891_, lean_object* v_a_892_, lean_object* v_x_893_){
_start:
{
uint8_t v___x_894_; 
v___x_894_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_892_, v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_892_ = stack[1].m_obj;
lean_object* v_x_893_ = stack[2].m_obj;
uint8_t v_res_895_;
v_res_895_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_box(0), v_a_892_, v_x_893_);
stack->m_num = v_res_895_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_896_, lean_object* v_a_897_, lean_object* v_x_898_){
_start:
{
uint8_t v_res_899_; lean_object* v_r_900_; 
v_res_899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(v_00_u03b2_896_, v_a_897_, v_x_898_);
lean_dec(v_x_898_);
lean_dec(v_a_897_);
v_r_900_ = lean_box(v_res_899_);
return v_r_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(lean_object* v_00_u03b2_901_, lean_object* v_data_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_data_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_904_, lean_object* v_i_905_, lean_object* v_source_906_, lean_object* v_target_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v_i_905_, v_source_906_, v_target_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_910_, v_x_911_);
return v___x_912_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object* v_m_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_buckets_915_; lean_object* v___x_916_; uint64_t v___y_918_; 
v_buckets_915_ = lean_ctor_get(v_m_913_, 1);
v___x_916_ = lean_array_get_size(v_buckets_915_);
if (lean_obj_tag(v_a_914_) == 0)
{
uint64_t v___x_932_; 
v___x_932_ = 1723ULL;
v___y_918_ = v___x_932_;
goto v___jp_917_;
}
else
{
uint64_t v_hash_933_; 
v_hash_933_ = lean_ctor_get_uint64(v_a_914_, sizeof(void*)*2);
v___y_918_ = v_hash_933_;
goto v___jp_917_;
}
v___jp_917_:
{
uint64_t v___x_919_; uint64_t v___x_920_; uint64_t v_fold_921_; uint64_t v___x_922_; uint64_t v___x_923_; uint64_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; size_t v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_919_ = 32ULL;
v___x_920_ = lean_uint64_shift_right(v___y_918_, v___x_919_);
v_fold_921_ = lean_uint64_xor(v___y_918_, v___x_920_);
v___x_922_ = 16ULL;
v___x_923_ = lean_uint64_shift_right(v_fold_921_, v___x_922_);
v___x_924_ = lean_uint64_xor(v_fold_921_, v___x_923_);
v___x_925_ = lean_uint64_to_usize(v___x_924_);
v___x_926_ = lean_usize_of_nat(v___x_916_);
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_sub(v___x_926_, v___x_927_);
v___x_929_ = lean_usize_land(v___x_925_, v___x_928_);
v___x_930_ = lean_array_uget_borrowed(v_buckets_915_, v___x_929_);
v___x_931_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_914_, v___x_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_913_ = stack[0].m_obj;
lean_object* v_a_914_ = stack[1].m_obj;
uint8_t v_res_934_;
v_res_934_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_913_, v_a_914_);
stack->m_num = v_res_934_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object* v_m_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_m_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
uint8_t l_Lean_NameHashSet_contains(lean_object* v_s_939_, lean_object* v_n_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_s_939_, v_n_940_);
return v___x_941_;
}
}
LEAN_EXPORT void l_Lean_NameHashSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_939_ = stack[0].m_obj;
lean_object* v_n_940_ = stack[1].m_obj;
uint8_t v_res_942_;
v_res_942_ = l_Lean_NameHashSet_contains(v_s_939_, v_n_940_);
stack->m_num = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object* v_s_943_, lean_object* v_n_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Lean_NameHashSet_contains(v_s_943_, v_n_944_);
lean_dec(v_n_944_);
lean_dec_ref(v_s_943_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object* v_00_u03b2_947_, lean_object* v_m_948_, lean_object* v_a_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_948_, v_a_949_);
return v___x_950_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_948_ = stack[1].m_obj;
lean_object* v_a_949_ = stack[2].m_obj;
uint8_t v_res_951_;
v_res_951_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_box(0), v_m_948_, v_a_949_);
stack->m_num = v_res_951_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object* v_00_u03b2_952_, lean_object* v_m_953_, lean_object* v_a_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(v_00_u03b2_952_, v_m_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_m_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object* v_f_957_, lean_object* v_acc_958_, lean_object* v_a_959_){
_start:
{
if (lean_obj_tag(v_a_959_) == 0)
{
lean_dec_ref(v_f_957_);
return v_acc_958_;
}
else
{
lean_object* v_key_960_; lean_object* v_value_961_; lean_object* v_tail_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_key_960_ = lean_ctor_get(v_a_959_, 0);
v_value_961_ = lean_ctor_get(v_a_959_, 1);
v_tail_962_ = lean_ctor_get(v_a_959_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_959_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v_a_959_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_tail_962_);
lean_inc(v_value_961_);
lean_inc(v_key_960_);
lean_dec(v_a_959_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
lean_inc_ref(v_f_957_);
lean_inc(v_key_960_);
v___x_966_ = lean_apply_1(v_f_957_, v_key_960_);
v___x_967_ = lean_unbox(v___x_966_);
if (v___x_967_ == 0)
{
lean_del_object(v___x_964_);
lean_dec(v_value_961_);
lean_dec(v_key_960_);
v_a_959_ = v_tail_962_;
goto _start;
}
else
{
lean_object* v___x_970_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 2, v_acc_958_);
v___x_970_ = v___x_964_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_key_960_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_value_961_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_acc_958_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v_acc_958_ = v___x_970_;
v_a_959_ = v_tail_962_;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(lean_object* v_f_974_, size_t v_sz_975_, size_t v_i_976_, lean_object* v_bs_977_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_lt(v_i_976_, v_sz_975_);
if (v___x_978_ == 0)
{
lean_dec_ref(v_f_974_);
return v_bs_977_;
}
else
{
lean_object* v_v_979_; lean_object* v___x_980_; lean_object* v_bs_x27_981_; lean_object* v___x_982_; lean_object* v___x_983_; size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v_v_979_ = lean_array_uget(v_bs_977_, v_i_976_);
v___x_980_ = lean_unsigned_to_nat(0u);
v_bs_x27_981_ = lean_array_uset(v_bs_977_, v_i_976_, v___x_980_);
v___x_982_ = lean_box(0);
lean_inc_ref(v_f_974_);
v___x_983_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_974_, v___x_982_, v_v_979_);
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_add(v_i_976_, v___x_984_);
v___x_986_ = lean_array_uset(v_bs_x27_981_, v_i_976_, v___x_983_);
v_i_976_ = v___x_985_;
v_bs_977_ = v___x_986_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_974_ = stack[0].m_obj;
size_t v_sz_975_ = stack[1].m_num;
size_t v_i_976_ = stack[2].m_num;
lean_object* v_bs_977_ = stack[3].m_obj;
lean_object* v_res_988_;
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_974_, v_sz_975_, v_i_976_, v_bs_977_);
stack->m_obj
 = v_res_988_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(lean_object* v_f_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_bs_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_994_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_989_, v_sz_boxed_993_, v_i_boxed_994_, v_bs_992_);
return v_res_995_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(lean_object* v_as_996_, size_t v_i_997_, size_t v_stop_998_, lean_object* v_b_999_){
_start:
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_usize_dec_eq(v_i_997_, v_stop_998_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; 
v___x_1001_ = lean_array_uget_borrowed(v_as_996_, v_i_997_);
v___x_1002_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_1001_);
v___x_1003_ = lean_nat_add(v_b_999_, v___x_1002_);
lean_dec(v___x_1002_);
lean_dec(v_b_999_);
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_add(v_i_997_, v___x_1004_);
v_i_997_ = v___x_1005_;
v_b_999_ = v___x_1003_;
goto _start;
}
else
{
return v_b_999_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_996_ = stack[0].m_obj;
size_t v_i_997_ = stack[1].m_num;
size_t v_stop_998_ = stack[2].m_num;
lean_object* v_b_999_ = stack[3].m_obj;
lean_object* v_res_1007_;
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_as_996_, v_i_997_, v_stop_998_, v_b_999_);
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(lean_object* v_as_1008_, lean_object* v_i_1009_, lean_object* v_stop_1010_, lean_object* v_b_1011_){
_start:
{
size_t v_i_boxed_1012_; size_t v_stop_boxed_1013_; lean_object* v_res_1014_; 
v_i_boxed_1012_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_stop_boxed_1013_ = lean_unbox_usize(v_stop_1010_);
lean_dec(v_stop_1010_);
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_as_1008_, v_i_boxed_1012_, v_stop_boxed_1013_, v_b_1011_);
lean_dec_ref(v_as_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object* v_f_1015_, lean_object* v_m_1016_){
_start:
{
lean_object* v_buckets_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1035_; 
v_buckets_1017_ = lean_ctor_get(v_m_1016_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_m_1016_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; 
v_unused_1036_ = lean_ctor_get(v_m_1016_, 0);
lean_dec(v_unused_1036_);
v___x_1019_ = v_m_1016_;
v_isShared_1020_ = v_isSharedCheck_1035_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_buckets_1017_);
lean_dec(v_m_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1035_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
size_t v_sz_1021_; size_t v___x_1022_; lean_object* v_newBuckets_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_sz_1021_ = lean_array_size(v_buckets_1017_);
v___x_1022_ = ((size_t)0ULL);
v_newBuckets_1023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_1015_, v_sz_1021_, v___x_1022_, v_buckets_1017_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_array_get_size(v_newBuckets_1023_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1028_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_newBuckets_1023_);
lean_ctor_set(v___x_1019_, 0, v___x_1024_);
v___x_1028_ = v___x_1019_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_newBuckets_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
else
{
size_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1030_ = lean_usize_of_nat(v___x_1025_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_1023_, v___x_1022_, v___x_1030_, v___x_1024_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_newBuckets_1023_);
lean_ctor_set(v___x_1019_, 0, v___x_1031_);
v___x_1033_ = v___x_1019_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_newBuckets_1023_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object* v_f_1037_, lean_object* v_s_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(v_f_1037_, v_s_1038_);
return v___x_1039_;
}
}
uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
if (lean_obj_tag(v_x_1040_) == 0)
{
if (lean_obj_tag(v_x_1041_) == 0)
{
uint8_t v___x_1042_; 
v___x_1042_ = 1;
return v___x_1042_;
}
else
{
uint8_t v___x_1043_; 
v___x_1043_ = 0;
return v___x_1043_;
}
}
else
{
if (lean_obj_tag(v_x_1041_) == 0)
{
uint8_t v___x_1044_; 
v___x_1044_ = 0;
return v___x_1044_;
}
else
{
lean_object* v_head_1045_; lean_object* v_tail_1046_; lean_object* v_head_1047_; lean_object* v_tail_1048_; uint8_t v___x_1049_; 
v_head_1045_ = lean_ctor_get(v_x_1040_, 0);
v_tail_1046_ = lean_ctor_get(v_x_1040_, 1);
v_head_1047_ = lean_ctor_get(v_x_1041_, 0);
v_tail_1048_ = lean_ctor_get(v_x_1041_, 1);
v___x_1049_ = lean_nat_dec_eq(v_head_1045_, v_head_1047_);
if (v___x_1049_ == 0)
{
return v___x_1049_;
}
else
{
v_x_1040_ = v_tail_1046_;
v_x_1041_ = v_tail_1048_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1040_ = stack[0].m_obj;
lean_object* v_x_1041_ = stack[1].m_obj;
uint8_t v_res_1051_;
v_res_1051_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_1040_, v_x_1041_);
stack->m_num = v_res_1051_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_1052_, v_x_1053_);
lean_dec(v_x_1053_);
lean_dec(v_x_1052_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object* v_v_u2081_1056_, lean_object* v_v_u2082_1057_){
_start:
{
lean_object* v_name_1058_; lean_object* v_imported_1059_; lean_object* v_ctx_1060_; lean_object* v_scopes_1061_; lean_object* v_name_1062_; lean_object* v_imported_1063_; lean_object* v_ctx_1064_; lean_object* v_scopes_1065_; uint8_t v___y_1067_; uint8_t v___x_1070_; 
v_name_1058_ = lean_ctor_get(v_v_u2081_1056_, 0);
v_imported_1059_ = lean_ctor_get(v_v_u2081_1056_, 1);
v_ctx_1060_ = lean_ctor_get(v_v_u2081_1056_, 2);
v_scopes_1061_ = lean_ctor_get(v_v_u2081_1056_, 3);
v_name_1062_ = lean_ctor_get(v_v_u2082_1057_, 0);
v_imported_1063_ = lean_ctor_get(v_v_u2082_1057_, 1);
v_ctx_1064_ = lean_ctor_get(v_v_u2082_1057_, 2);
v_scopes_1065_ = lean_ctor_get(v_v_u2082_1057_, 3);
v___x_1070_ = l_Lean_Name_isPrefixOf(v_name_1058_, v_name_1062_);
if (v___x_1070_ == 0)
{
v___y_1067_ = v___x_1070_;
goto v___jp_1066_;
}
else
{
uint8_t v___x_1071_; 
v___x_1071_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1061_, v_scopes_1065_);
v___y_1067_ = v___x_1071_;
goto v___jp_1066_;
}
v___jp_1066_:
{
if (v___y_1067_ == 0)
{
return v___y_1067_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_name_eq(v_ctx_1060_, v_ctx_1064_);
if (v___x_1068_ == 0)
{
return v___x_1068_;
}
else
{
uint8_t v___x_1069_; 
v___x_1069_ = lean_name_eq(v_imported_1059_, v_imported_1063_);
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MacroScopesView_isPrefixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_u2081_1056_ = stack[0].m_obj;
lean_object* v_v_u2082_1057_ = stack[1].m_obj;
uint8_t v_res_1072_;
v_res_1072_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_1056_, v_v_u2082_1057_);
stack->m_num = v_res_1072_;
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object* v_v_u2081_1073_, lean_object* v_v_u2082_1074_){
_start:
{
uint8_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_1073_, v_v_u2082_1074_);
lean_dec_ref(v_v_u2082_1074_);
lean_dec_ref(v_v_u2081_1073_);
v_r_1076_ = lean_box(v_res_1075_);
return v_r_1076_;
}
}
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object* v_v_u2081_1077_, lean_object* v_v_u2082_1078_){
_start:
{
lean_object* v_name_1079_; lean_object* v_imported_1080_; lean_object* v_ctx_1081_; lean_object* v_scopes_1082_; lean_object* v_name_1083_; lean_object* v_imported_1084_; lean_object* v_ctx_1085_; lean_object* v_scopes_1086_; uint8_t v___y_1088_; uint8_t v___x_1091_; 
v_name_1079_ = lean_ctor_get(v_v_u2081_1077_, 0);
v_imported_1080_ = lean_ctor_get(v_v_u2081_1077_, 1);
v_ctx_1081_ = lean_ctor_get(v_v_u2081_1077_, 2);
v_scopes_1082_ = lean_ctor_get(v_v_u2081_1077_, 3);
v_name_1083_ = lean_ctor_get(v_v_u2082_1078_, 0);
v_imported_1084_ = lean_ctor_get(v_v_u2082_1078_, 1);
v_ctx_1085_ = lean_ctor_get(v_v_u2082_1078_, 2);
v_scopes_1086_ = lean_ctor_get(v_v_u2082_1078_, 3);
v___x_1091_ = l_Lean_Name_isSuffixOf(v_name_1079_, v_name_1083_);
if (v___x_1091_ == 0)
{
v___y_1088_ = v___x_1091_;
goto v___jp_1087_;
}
else
{
uint8_t v___x_1092_; 
v___x_1092_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1082_, v_scopes_1086_);
v___y_1088_ = v___x_1092_;
goto v___jp_1087_;
}
v___jp_1087_:
{
if (v___y_1088_ == 0)
{
return v___y_1088_;
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = lean_name_eq(v_ctx_1081_, v_ctx_1085_);
if (v___x_1089_ == 0)
{
return v___x_1089_;
}
else
{
uint8_t v___x_1090_; 
v___x_1090_ = lean_name_eq(v_imported_1080_, v_imported_1084_);
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MacroScopesView_isSuffixOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_u2081_1077_ = stack[0].m_obj;
lean_object* v_v_u2082_1078_ = stack[1].m_obj;
uint8_t v_res_1093_;
v_res_1093_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_1077_, v_v_u2082_1078_);
stack->m_num = v_res_1093_;
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object* v_v_u2081_1094_, lean_object* v_v_u2082_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_1094_, v_v_u2082_1095_);
lean_dec_ref(v_v_u2082_1095_);
lean_dec_ref(v_v_u2081_1094_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
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
