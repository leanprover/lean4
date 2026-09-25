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
LEAN_EXPORT lean_object* l_Lean_mkNameMap___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(1);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNameMap___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_mkNameMap___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNameMap(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(1);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___lam__0(lean_object* v_x1_7_, lean_object* v_x2_8_, lean_object* v_x3_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_x1_7_);
lean_ctor_set(v___x_10_, 1, v_x2_8_);
v___x_11_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v_x3_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg(lean_object* v_inst_36_, lean_object* v_m_37_, lean_object* v_prec_38_){
_start:
{
lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___f_39_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__0));
v___x_40_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__1));
v___x_41_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__3));
v___f_42_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_42_, 0, v_inst_36_);
v___x_43_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_43_, 0, lean_box(0));
lean_closure_set(v___x_43_, 1, lean_box(0));
lean_closure_set(v___x_43_, 2, v___x_40_);
lean_closure_set(v___x_43_, 3, v___f_42_);
v___x_44_ = lean_box(0);
v___x_45_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__13));
v___x_46_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_45_, v___f_39_, v___x_44_, v_m_37_);
v___x_47_ = l_List_repr___redArg(v___x_43_, v___x_46_);
v___x_48_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_41_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
v___x_49_ = l_Repr_addAppParen(v___x_48_, v_prec_38_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___redArg___boxed(lean_object* v_inst_50_, lean_object* v_m_51_, lean_object* v_prec_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_NameMap_instRepr___aux__1___redArg(v_inst_50_, v_m_51_, v_prec_52_);
lean_dec(v_prec_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1(lean_object* v_00_u03b1_54_, lean_object* v_inst_55_, lean_object* v_m_56_, lean_object* v_prec_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___f_58_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__0));
v___x_59_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__1));
v___x_60_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__3));
v___f_61_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_61_, 0, v_inst_55_);
v___x_62_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_62_, 0, lean_box(0));
lean_closure_set(v___x_62_, 1, lean_box(0));
lean_closure_set(v___x_62_, 2, v___x_59_);
lean_closure_set(v___x_62_, 3, v___f_61_);
v___x_63_ = lean_box(0);
v___x_64_ = ((lean_object*)(l_Lean_NameMap_instRepr___aux__1___redArg___closed__13));
v___x_65_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_64_, v___f_58_, v___x_63_, v_m_56_);
v___x_66_ = l_List_repr___redArg(v___x_62_, v___x_65_);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_60_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = l_Repr_addAppParen(v___x_67_, v_prec_57_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___aux__1___boxed(lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_m_71_, lean_object* v_prec_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_NameMap_instRepr___aux__1(v_00_u03b1_69_, v_inst_70_, v_m_71_, v_prec_72_);
lean_dec(v_prec_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr___redArg(lean_object* v_inst_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_alloc_closure((void*)(l_Lean_NameMap_instRepr___aux__1___boxed), 4, 2);
lean_closure_set(v___x_75_, 0, lean_box(0));
lean_closure_set(v___x_75_, 1, v_inst_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instRepr(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_closure((void*)(l_Lean_NameMap_instRepr___aux__1___boxed), 4, 2);
lean_closure_set(v___x_78_, 0, lean_box(0));
lean_closure_set(v___x_78_, 1, v_inst_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(1);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_NameMap_instEmptyCollection___redArg();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instEmptyCollection(lean_object* v_00_u03b1_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(1);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(1);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited___redArg___boxed(lean_object* v___dummy_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_NameMap_instInhabited___redArg();
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInhabited(lean_object* v_00_u03b1_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(1);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object* v_k_91_, lean_object* v_v_92_, lean_object* v_t_93_){
_start:
{
if (lean_obj_tag(v_t_93_) == 0)
{
lean_object* v_size_94_; lean_object* v_k_95_; lean_object* v_v_96_; lean_object* v_l_97_; lean_object* v_r_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_378_; 
v_size_94_ = lean_ctor_get(v_t_93_, 0);
v_k_95_ = lean_ctor_get(v_t_93_, 1);
v_v_96_ = lean_ctor_get(v_t_93_, 2);
v_l_97_ = lean_ctor_get(v_t_93_, 3);
v_r_98_ = lean_ctor_get(v_t_93_, 4);
v_isSharedCheck_378_ = !lean_is_exclusive(v_t_93_);
if (v_isSharedCheck_378_ == 0)
{
v___x_100_ = v_t_93_;
v_isShared_101_ = v_isSharedCheck_378_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_r_98_);
lean_inc(v_l_97_);
lean_inc(v_v_96_);
lean_inc(v_k_95_);
lean_inc(v_size_94_);
lean_dec(v_t_93_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_378_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
uint8_t v___x_102_; 
v___x_102_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_91_, v_k_95_);
switch(v___x_102_)
{
case 0:
{
lean_object* v_impl_103_; lean_object* v___x_104_; 
lean_dec(v_size_94_);
v_impl_103_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_91_, v_v_92_, v_l_97_);
v___x_104_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_98_) == 0)
{
lean_object* v_size_105_; lean_object* v_size_106_; lean_object* v_k_107_; lean_object* v_v_108_; lean_object* v_l_109_; lean_object* v_r_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_size_105_ = lean_ctor_get(v_r_98_, 0);
v_size_106_ = lean_ctor_get(v_impl_103_, 0);
lean_inc(v_size_106_);
v_k_107_ = lean_ctor_get(v_impl_103_, 1);
lean_inc(v_k_107_);
v_v_108_ = lean_ctor_get(v_impl_103_, 2);
lean_inc(v_v_108_);
v_l_109_ = lean_ctor_get(v_impl_103_, 3);
lean_inc(v_l_109_);
v_r_110_ = lean_ctor_get(v_impl_103_, 4);
lean_inc(v_r_110_);
v___x_111_ = lean_unsigned_to_nat(3u);
v___x_112_ = lean_nat_mul(v___x_111_, v_size_105_);
v___x_113_ = lean_nat_dec_lt(v___x_112_, v_size_106_);
lean_dec(v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec(v_r_110_);
lean_dec(v_l_109_);
lean_dec(v_v_108_);
lean_dec(v_k_107_);
v___x_114_ = lean_nat_add(v___x_104_, v_size_106_);
lean_dec(v_size_106_);
v___x_115_ = lean_nat_add(v___x_114_, v_size_105_);
lean_dec(v___x_114_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 3, v_impl_103_);
lean_ctor_set(v___x_100_, 0, v___x_115_);
v___x_117_ = v___x_100_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v_impl_103_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v_r_98_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
else
{
lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_184_; 
v_isSharedCheck_184_ = !lean_is_exclusive(v_impl_103_);
if (v_isSharedCheck_184_ == 0)
{
lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; 
v_unused_185_ = lean_ctor_get(v_impl_103_, 4);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_impl_103_, 3);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_impl_103_, 2);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_impl_103_, 1);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_impl_103_, 0);
lean_dec(v_unused_189_);
v___x_120_ = v_impl_103_;
v_isShared_121_ = v_isSharedCheck_184_;
goto v_resetjp_119_;
}
else
{
lean_dec(v_impl_103_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_184_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_size_122_; lean_object* v_size_123_; lean_object* v_k_124_; lean_object* v_v_125_; lean_object* v_l_126_; lean_object* v_r_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_size_122_ = lean_ctor_get(v_l_109_, 0);
v_size_123_ = lean_ctor_get(v_r_110_, 0);
v_k_124_ = lean_ctor_get(v_r_110_, 1);
v_v_125_ = lean_ctor_get(v_r_110_, 2);
v_l_126_ = lean_ctor_get(v_r_110_, 3);
v_r_127_ = lean_ctor_get(v_r_110_, 4);
v___x_128_ = lean_unsigned_to_nat(2u);
v___x_129_ = lean_nat_mul(v___x_128_, v_size_122_);
v___x_130_ = lean_nat_dec_lt(v_size_123_, v___x_129_);
lean_dec(v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_159_; 
lean_inc(v_r_127_);
lean_inc(v_l_126_);
lean_inc(v_v_125_);
lean_inc(v_k_124_);
v_isSharedCheck_159_ = !lean_is_exclusive(v_r_110_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; lean_object* v_unused_161_; lean_object* v_unused_162_; lean_object* v_unused_163_; lean_object* v_unused_164_; 
v_unused_160_ = lean_ctor_get(v_r_110_, 4);
lean_dec(v_unused_160_);
v_unused_161_ = lean_ctor_get(v_r_110_, 3);
lean_dec(v_unused_161_);
v_unused_162_ = lean_ctor_get(v_r_110_, 2);
lean_dec(v_unused_162_);
v_unused_163_ = lean_ctor_get(v_r_110_, 1);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_r_110_, 0);
lean_dec(v_unused_164_);
v___x_132_ = v_r_110_;
v_isShared_133_ = v_isSharedCheck_159_;
goto v_resetjp_131_;
}
else
{
lean_dec(v_r_110_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_159_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___y_137_; lean_object* v___y_138_; lean_object* v___y_139_; lean_object* v___x_147_; lean_object* v___y_149_; 
v___x_134_ = lean_nat_add(v___x_104_, v_size_106_);
lean_dec(v_size_106_);
v___x_135_ = lean_nat_add(v___x_134_, v_size_105_);
lean_dec(v___x_134_);
v___x_147_ = lean_nat_add(v___x_104_, v_size_122_);
if (lean_obj_tag(v_l_126_) == 0)
{
lean_object* v_size_157_; 
v_size_157_ = lean_ctor_get(v_l_126_, 0);
lean_inc(v_size_157_);
v___y_149_ = v_size_157_;
goto v___jp_148_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___y_149_ = v___x_158_;
goto v___jp_148_;
}
v___jp_136_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_nat_add(v___y_137_, v___y_139_);
lean_dec(v___y_139_);
lean_dec(v___y_137_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 4, v_r_98_);
lean_ctor_set(v___x_132_, 3, v_r_127_);
lean_ctor_set(v___x_132_, 2, v_v_96_);
lean_ctor_set(v___x_132_, 1, v_k_95_);
lean_ctor_set(v___x_132_, 0, v___x_140_);
v___x_142_ = v___x_132_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v_r_127_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_r_98_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 4, v___x_142_);
lean_ctor_set(v___x_120_, 3, v___y_138_);
lean_ctor_set(v___x_120_, 2, v_v_125_);
lean_ctor_set(v___x_120_, 1, v_k_124_);
lean_ctor_set(v___x_120_, 0, v___x_135_);
v___x_144_ = v___x_120_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_k_124_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_v_125_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v___y_138_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = lean_nat_add(v___x_147_, v___y_149_);
lean_dec(v___y_149_);
lean_dec(v___x_147_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v_l_126_);
lean_ctor_set(v___x_100_, 3, v_l_109_);
lean_ctor_set(v___x_100_, 2, v_v_108_);
lean_ctor_set(v___x_100_, 1, v_k_107_);
lean_ctor_set(v___x_100_, 0, v___x_150_);
v___x_152_ = v___x_100_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_l_126_);
v___x_152_ = v_reuseFailAlloc_156_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_nat_add(v___x_104_, v_size_105_);
if (lean_obj_tag(v_r_127_) == 0)
{
lean_object* v_size_154_; 
v_size_154_ = lean_ctor_get(v_r_127_, 0);
lean_inc(v_size_154_);
v___y_137_ = v___x_153_;
v___y_138_ = v___x_152_;
v___y_139_ = v_size_154_;
goto v___jp_136_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___y_137_ = v___x_153_;
v___y_138_ = v___x_152_;
v___y_139_ = v___x_155_;
goto v___jp_136_;
}
}
}
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
lean_del_object(v___x_100_);
v___x_165_ = lean_nat_add(v___x_104_, v_size_106_);
lean_dec(v_size_106_);
v___x_166_ = lean_nat_add(v___x_165_, v_size_105_);
lean_dec(v___x_165_);
v___x_167_ = lean_nat_add(v___x_104_, v_size_105_);
v___x_168_ = lean_nat_add(v___x_167_, v_size_123_);
lean_dec(v___x_167_);
lean_inc_ref(v_r_98_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 4, v_r_98_);
lean_ctor_set(v___x_120_, 3, v_r_110_);
lean_ctor_set(v___x_120_, 2, v_v_96_);
lean_ctor_set(v___x_120_, 1, v_k_95_);
lean_ctor_set(v___x_120_, 0, v___x_168_);
v___x_170_ = v___x_120_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_r_110_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v_r_98_);
v___x_170_ = v_reuseFailAlloc_183_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_isSharedCheck_177_ = !lean_is_exclusive(v_r_98_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; lean_object* v_unused_179_; lean_object* v_unused_180_; lean_object* v_unused_181_; lean_object* v_unused_182_; 
v_unused_178_ = lean_ctor_get(v_r_98_, 4);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_r_98_, 3);
lean_dec(v_unused_179_);
v_unused_180_ = lean_ctor_get(v_r_98_, 2);
lean_dec(v_unused_180_);
v_unused_181_ = lean_ctor_get(v_r_98_, 1);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_r_98_, 0);
lean_dec(v_unused_182_);
v___x_172_ = v_r_98_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_dec(v_r_98_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 4, v___x_170_);
lean_ctor_set(v___x_172_, 3, v_l_109_);
lean_ctor_set(v___x_172_, 2, v_v_108_);
lean_ctor_set(v___x_172_, 1, v_k_107_);
lean_ctor_set(v___x_172_, 0, v___x_166_);
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_107_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_l_109_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v___x_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_190_; 
v_l_190_ = lean_ctor_get(v_impl_103_, 3);
lean_inc(v_l_190_);
if (lean_obj_tag(v_l_190_) == 0)
{
lean_object* v_r_191_; lean_object* v_k_192_; lean_object* v_v_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_204_; 
v_r_191_ = lean_ctor_get(v_impl_103_, 4);
v_k_192_ = lean_ctor_get(v_impl_103_, 1);
v_v_193_ = lean_ctor_get(v_impl_103_, 2);
v_isSharedCheck_204_ = !lean_is_exclusive(v_impl_103_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; lean_object* v_unused_206_; 
v_unused_205_ = lean_ctor_get(v_impl_103_, 3);
lean_dec(v_unused_205_);
v_unused_206_ = lean_ctor_get(v_impl_103_, 0);
lean_dec(v_unused_206_);
v___x_195_ = v_impl_103_;
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_r_191_);
lean_inc(v_v_193_);
lean_inc(v_k_192_);
lean_dec(v_impl_103_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_204_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 3, v_r_191_);
lean_ctor_set(v___x_195_, 2, v_v_96_);
lean_ctor_set(v___x_195_, 1, v_k_95_);
lean_ctor_set(v___x_195_, 0, v___x_104_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_r_191_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v_r_191_);
v___x_199_ = v_reuseFailAlloc_203_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v___x_199_);
lean_ctor_set(v___x_100_, 3, v_l_190_);
lean_ctor_set(v___x_100_, 2, v_v_193_);
lean_ctor_set(v___x_100_, 1, v_k_192_);
lean_ctor_set(v___x_100_, 0, v___x_197_);
v___x_201_ = v___x_100_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_k_192_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_v_193_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_l_190_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_r_207_; 
v_r_207_ = lean_ctor_get(v_impl_103_, 4);
lean_inc(v_r_207_);
if (lean_obj_tag(v_r_207_) == 0)
{
lean_object* v_k_208_; lean_object* v_v_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_232_; 
v_k_208_ = lean_ctor_get(v_impl_103_, 1);
v_v_209_ = lean_ctor_get(v_impl_103_, 2);
v_isSharedCheck_232_ = !lean_is_exclusive(v_impl_103_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; lean_object* v_unused_234_; lean_object* v_unused_235_; 
v_unused_233_ = lean_ctor_get(v_impl_103_, 4);
lean_dec(v_unused_233_);
v_unused_234_ = lean_ctor_get(v_impl_103_, 3);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_impl_103_, 0);
lean_dec(v_unused_235_);
v___x_211_ = v_impl_103_;
v_isShared_212_ = v_isSharedCheck_232_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_v_209_);
lean_inc(v_k_208_);
lean_dec(v_impl_103_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_232_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_k_213_; lean_object* v_v_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_228_; 
v_k_213_ = lean_ctor_get(v_r_207_, 1);
v_v_214_ = lean_ctor_get(v_r_207_, 2);
v_isSharedCheck_228_ = !lean_is_exclusive(v_r_207_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_229_ = lean_ctor_get(v_r_207_, 4);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_r_207_, 3);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_r_207_, 0);
lean_dec(v_unused_231_);
v___x_216_ = v_r_207_;
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_v_214_);
lean_inc(v_k_213_);
lean_dec(v_r_207_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_228_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_unsigned_to_nat(3u);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 4, v_l_190_);
lean_ctor_set(v___x_216_, 3, v_l_190_);
lean_ctor_set(v___x_216_, 2, v_v_209_);
lean_ctor_set(v___x_216_, 1, v_k_208_);
lean_ctor_set(v___x_216_, 0, v___x_104_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_k_208_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_v_209_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_l_190_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_l_190_);
v___x_220_ = v_reuseFailAlloc_227_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 4, v_l_190_);
lean_ctor_set(v___x_211_, 2, v_v_96_);
lean_ctor_set(v___x_211_, 1, v_k_95_);
lean_ctor_set(v___x_211_, 0, v___x_104_);
v___x_222_ = v___x_211_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_l_190_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v_l_190_);
v___x_222_ = v_reuseFailAlloc_226_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_224_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v___x_222_);
lean_ctor_set(v___x_100_, 3, v___x_220_);
lean_ctor_set(v___x_100_, 2, v_v_214_);
lean_ctor_set(v___x_100_, 1, v_k_213_);
lean_ctor_set(v___x_100_, 0, v___x_218_);
v___x_224_ = v___x_100_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_k_213_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_v_214_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_236_ = lean_unsigned_to_nat(2u);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v_r_207_);
lean_ctor_set(v___x_100_, 3, v_impl_103_);
lean_ctor_set(v___x_100_, 0, v___x_236_);
v___x_238_ = v___x_100_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_impl_103_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_r_207_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
case 1:
{
lean_object* v___x_241_; 
lean_dec(v_v_96_);
lean_dec(v_k_95_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 2, v_v_92_);
lean_ctor_set(v___x_100_, 1, v_k_91_);
v___x_241_ = v___x_100_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_size_94_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_k_91_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_v_92_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_l_97_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_r_98_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
default: 
{
lean_object* v_impl_243_; lean_object* v___x_244_; 
lean_dec(v_size_94_);
v_impl_243_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_91_, v_v_92_, v_r_98_);
v___x_244_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_97_) == 0)
{
lean_object* v_size_245_; lean_object* v_size_246_; lean_object* v_k_247_; lean_object* v_v_248_; lean_object* v_l_249_; lean_object* v_r_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_size_245_ = lean_ctor_get(v_l_97_, 0);
v_size_246_ = lean_ctor_get(v_impl_243_, 0);
lean_inc(v_size_246_);
v_k_247_ = lean_ctor_get(v_impl_243_, 1);
lean_inc(v_k_247_);
v_v_248_ = lean_ctor_get(v_impl_243_, 2);
lean_inc(v_v_248_);
v_l_249_ = lean_ctor_get(v_impl_243_, 3);
lean_inc(v_l_249_);
v_r_250_ = lean_ctor_get(v_impl_243_, 4);
lean_inc(v_r_250_);
v___x_251_ = lean_unsigned_to_nat(3u);
v___x_252_ = lean_nat_mul(v___x_251_, v_size_245_);
v___x_253_ = lean_nat_dec_lt(v___x_252_, v_size_246_);
lean_dec(v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec(v_r_250_);
lean_dec(v_l_249_);
lean_dec(v_v_248_);
lean_dec(v_k_247_);
v___x_254_ = lean_nat_add(v___x_244_, v_size_245_);
v___x_255_ = lean_nat_add(v___x_254_, v_size_246_);
lean_dec(v_size_246_);
lean_dec(v___x_254_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v_impl_243_);
lean_ctor_set(v___x_100_, 0, v___x_255_);
v___x_257_ = v___x_100_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_258_, 3, v_l_97_);
lean_ctor_set(v_reuseFailAlloc_258_, 4, v_impl_243_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
else
{
lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_322_; 
v_isSharedCheck_322_ = !lean_is_exclusive(v_impl_243_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; lean_object* v_unused_327_; 
v_unused_323_ = lean_ctor_get(v_impl_243_, 4);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_impl_243_, 3);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_impl_243_, 2);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_impl_243_, 1);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_impl_243_, 0);
lean_dec(v_unused_327_);
v___x_260_ = v_impl_243_;
v_isShared_261_ = v_isSharedCheck_322_;
goto v_resetjp_259_;
}
else
{
lean_dec(v_impl_243_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_322_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_size_262_; lean_object* v_k_263_; lean_object* v_v_264_; lean_object* v_l_265_; lean_object* v_r_266_; lean_object* v_size_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v_size_262_ = lean_ctor_get(v_l_249_, 0);
v_k_263_ = lean_ctor_get(v_l_249_, 1);
v_v_264_ = lean_ctor_get(v_l_249_, 2);
v_l_265_ = lean_ctor_get(v_l_249_, 3);
v_r_266_ = lean_ctor_get(v_l_249_, 4);
v_size_267_ = lean_ctor_get(v_r_250_, 0);
v___x_268_ = lean_unsigned_to_nat(2u);
v___x_269_ = lean_nat_mul(v___x_268_, v_size_267_);
v___x_270_ = lean_nat_dec_lt(v_size_262_, v___x_269_);
lean_dec(v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_298_; 
lean_inc(v_r_266_);
lean_inc(v_l_265_);
lean_inc(v_v_264_);
lean_inc(v_k_263_);
v_isSharedCheck_298_ = !lean_is_exclusive(v_l_249_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; 
v_unused_299_ = lean_ctor_get(v_l_249_, 4);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_l_249_, 3);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_l_249_, 2);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_l_249_, 1);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_l_249_, 0);
lean_dec(v_unused_303_);
v___x_272_ = v_l_249_;
v_isShared_273_ = v_isSharedCheck_298_;
goto v_resetjp_271_;
}
else
{
lean_dec(v_l_249_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_298_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_288_; 
v___x_274_ = lean_nat_add(v___x_244_, v_size_245_);
v___x_275_ = lean_nat_add(v___x_274_, v_size_246_);
lean_dec(v_size_246_);
if (lean_obj_tag(v_l_265_) == 0)
{
lean_object* v_size_296_; 
v_size_296_ = lean_ctor_get(v_l_265_, 0);
lean_inc(v_size_296_);
v___y_288_ = v_size_296_;
goto v___jp_287_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___y_288_ = v___x_297_;
goto v___jp_287_;
}
v___jp_276_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_nat_add(v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec(v___y_278_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 4, v_r_250_);
lean_ctor_set(v___x_272_, 3, v_r_266_);
lean_ctor_set(v___x_272_, 2, v_v_248_);
lean_ctor_set(v___x_272_, 1, v_k_247_);
lean_ctor_set(v___x_272_, 0, v___x_280_);
v___x_282_ = v___x_272_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_280_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_k_247_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_v_248_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_r_266_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_r_250_);
v___x_282_ = v_reuseFailAlloc_286_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_284_; 
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 4, v___x_282_);
lean_ctor_set(v___x_260_, 3, v___y_277_);
lean_ctor_set(v___x_260_, 2, v_v_264_);
lean_ctor_set(v___x_260_, 1, v_k_263_);
lean_ctor_set(v___x_260_, 0, v___x_275_);
v___x_284_ = v___x_260_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_k_263_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_v_264_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v___y_277_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_nat_add(v___x_274_, v___y_288_);
lean_dec(v___y_288_);
lean_dec(v___x_274_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v_l_265_);
lean_ctor_set(v___x_100_, 0, v___x_289_);
v___x_291_ = v___x_100_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_295_, 3, v_l_97_);
lean_ctor_set(v_reuseFailAlloc_295_, 4, v_l_265_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_nat_add(v___x_244_, v_size_267_);
if (lean_obj_tag(v_r_266_) == 0)
{
lean_object* v_size_293_; 
v_size_293_ = lean_ctor_get(v_r_266_, 0);
lean_inc(v_size_293_);
v___y_277_ = v___x_291_;
v___y_278_ = v___x_292_;
v___y_279_ = v_size_293_;
goto v___jp_276_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___y_277_ = v___x_291_;
v___y_278_ = v___x_292_;
v___y_279_ = v___x_294_;
goto v___jp_276_;
}
}
}
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
lean_del_object(v___x_100_);
v___x_304_ = lean_nat_add(v___x_244_, v_size_245_);
v___x_305_ = lean_nat_add(v___x_304_, v_size_246_);
lean_dec(v_size_246_);
v___x_306_ = lean_nat_add(v___x_304_, v_size_262_);
lean_dec(v___x_304_);
lean_inc_ref(v_l_97_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 4, v_l_249_);
lean_ctor_set(v___x_260_, 3, v_l_97_);
lean_ctor_set(v___x_260_, 2, v_v_96_);
lean_ctor_set(v___x_260_, 1, v_k_95_);
lean_ctor_set(v___x_260_, 0, v___x_306_);
v___x_308_ = v___x_260_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_l_97_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_l_249_);
v___x_308_ = v_reuseFailAlloc_321_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_isSharedCheck_315_ = !lean_is_exclusive(v_l_97_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; 
v_unused_316_ = lean_ctor_get(v_l_97_, 4);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_l_97_, 3);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_l_97_, 2);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_l_97_, 1);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_l_97_, 0);
lean_dec(v_unused_320_);
v___x_310_ = v_l_97_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_dec(v_l_97_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_250_);
lean_ctor_set(v___x_310_, 3, v___x_308_);
lean_ctor_set(v___x_310_, 2, v_v_248_);
lean_ctor_set(v___x_310_, 1, v_k_247_);
lean_ctor_set(v___x_310_, 0, v___x_305_);
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_k_247_);
lean_ctor_set(v_reuseFailAlloc_314_, 2, v_v_248_);
lean_ctor_set(v_reuseFailAlloc_314_, 3, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_314_, 4, v_r_250_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_328_; 
v_l_328_ = lean_ctor_get(v_impl_243_, 3);
lean_inc(v_l_328_);
if (lean_obj_tag(v_l_328_) == 0)
{
lean_object* v_r_329_; lean_object* v_k_330_; lean_object* v_v_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_354_; 
v_r_329_ = lean_ctor_get(v_impl_243_, 4);
v_k_330_ = lean_ctor_get(v_impl_243_, 1);
v_v_331_ = lean_ctor_get(v_impl_243_, 2);
v_isSharedCheck_354_ = !lean_is_exclusive(v_impl_243_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_355_ = lean_ctor_get(v_impl_243_, 3);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_243_, 0);
lean_dec(v_unused_356_);
v___x_333_ = v_impl_243_;
v_isShared_334_ = v_isSharedCheck_354_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_r_329_);
lean_inc(v_v_331_);
lean_inc(v_k_330_);
lean_dec(v_impl_243_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_354_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_k_335_; lean_object* v_v_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_350_; 
v_k_335_ = lean_ctor_get(v_l_328_, 1);
v_v_336_ = lean_ctor_get(v_l_328_, 2);
v_isSharedCheck_350_ = !lean_is_exclusive(v_l_328_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; lean_object* v_unused_352_; lean_object* v_unused_353_; 
v_unused_351_ = lean_ctor_get(v_l_328_, 4);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_l_328_, 3);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_l_328_, 0);
lean_dec(v_unused_353_);
v___x_338_ = v_l_328_;
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_v_336_);
lean_inc(v_k_335_);
lean_dec(v_l_328_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_350_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_329_, 2);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 4, v_r_329_);
lean_ctor_set(v___x_338_, 3, v_r_329_);
lean_ctor_set(v___x_338_, 2, v_v_96_);
lean_ctor_set(v___x_338_, 1, v_k_95_);
lean_ctor_set(v___x_338_, 0, v___x_244_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_r_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_r_329_);
v___x_342_ = v_reuseFailAlloc_349_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
lean_inc(v_r_329_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 3, v_r_329_);
lean_ctor_set(v___x_333_, 0, v___x_244_);
v___x_344_ = v___x_333_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_k_330_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_v_331_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_r_329_);
lean_ctor_set(v_reuseFailAlloc_348_, 4, v_r_329_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v___x_344_);
lean_ctor_set(v___x_100_, 3, v___x_342_);
lean_ctor_set(v___x_100_, 2, v_v_336_);
lean_ctor_set(v___x_100_, 1, v_k_335_);
lean_ctor_set(v___x_100_, 0, v___x_340_);
v___x_346_ = v___x_100_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_335_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_v_336_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
else
{
lean_object* v_r_357_; 
v_r_357_ = lean_ctor_get(v_impl_243_, 4);
lean_inc(v_r_357_);
if (lean_obj_tag(v_r_357_) == 0)
{
lean_object* v_k_358_; lean_object* v_v_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_370_; 
v_k_358_ = lean_ctor_get(v_impl_243_, 1);
v_v_359_ = lean_ctor_get(v_impl_243_, 2);
v_isSharedCheck_370_ = !lean_is_exclusive(v_impl_243_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_371_ = lean_ctor_get(v_impl_243_, 4);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_impl_243_, 3);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_impl_243_, 0);
lean_dec(v_unused_373_);
v___x_361_ = v_impl_243_;
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_v_359_);
lean_inc(v_k_358_);
lean_dec(v_impl_243_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_unsigned_to_nat(3u);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 4, v_l_328_);
lean_ctor_set(v___x_361_, 2, v_v_96_);
lean_ctor_set(v___x_361_, 1, v_k_95_);
lean_ctor_set(v___x_361_, 0, v___x_244_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_l_328_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_l_328_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v_r_357_);
lean_ctor_set(v___x_100_, 3, v___x_365_);
lean_ctor_set(v___x_100_, 2, v_v_359_);
lean_ctor_set(v___x_100_, 1, v_k_358_);
lean_ctor_set(v___x_100_, 0, v___x_363_);
v___x_367_ = v___x_100_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_k_358_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_v_359_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_r_357_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_unsigned_to_nat(2u);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 4, v_impl_243_);
lean_ctor_set(v___x_100_, 3, v_r_357_);
lean_ctor_set(v___x_100_, 0, v___x_374_);
v___x_376_ = v___x_100_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_k_95_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v_v_96_);
lean_ctor_set(v_reuseFailAlloc_377_, 3, v_r_357_);
lean_ctor_set(v_reuseFailAlloc_377_, 4, v_impl_243_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
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
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_k_91_);
lean_ctor_set(v___x_380_, 2, v_v_92_);
lean_ctor_set(v___x_380_, 3, v_t_93_);
lean_ctor_set(v___x_380_, 4, v_t_93_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert___redArg(lean_object* v_m_381_, lean_object* v_n_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_382_, v_a_383_, v_m_381_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_insert(lean_object* v_00_u03b1_385_, lean_object* v_m_386_, lean_object* v_n_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_387_, v_a_388_, v_m_386_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0(lean_object* v_00_u03b2_390_, lean_object* v_k_391_, lean_object* v_v_392_, lean_object* v_t_393_, lean_object* v_hl_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_391_, v_v_392_, v_t_393_);
return v___x_395_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object* v_k_396_, lean_object* v_t_397_){
_start:
{
if (lean_obj_tag(v_t_397_) == 0)
{
lean_object* v_k_398_; lean_object* v_l_399_; lean_object* v_r_400_; uint8_t v___x_401_; 
v_k_398_ = lean_ctor_get(v_t_397_, 1);
v_l_399_ = lean_ctor_get(v_t_397_, 3);
v_r_400_ = lean_ctor_get(v_t_397_, 4);
v___x_401_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_396_, v_k_398_);
switch(v___x_401_)
{
case 0:
{
v_t_397_ = v_l_399_;
goto _start;
}
case 1:
{
uint8_t v___x_403_; 
v___x_403_ = 1;
return v___x_403_;
}
default: 
{
v_t_397_ = v_r_400_;
goto _start;
}
}
}
else
{
uint8_t v___x_405_; 
v___x_405_ = 0;
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg___boxed(lean_object* v_k_406_, lean_object* v_t_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_406_, v_t_407_);
lean_dec(v_t_407_);
lean_dec(v_k_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains___redArg(lean_object* v_m_410_, lean_object* v_n_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_411_, v_m_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___redArg___boxed(lean_object* v_m_413_, lean_object* v_n_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Lean_NameMap_contains___redArg(v_m_413_, v_n_414_);
lean_dec(v_n_414_);
lean_dec(v_m_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_contains(lean_object* v_00_u03b1_417_, lean_object* v_m_418_, lean_object* v_n_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_419_, v_m_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_contains___boxed(lean_object* v_00_u03b1_421_, lean_object* v_m_422_, lean_object* v_n_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Lean_NameMap_contains(v_00_u03b1_421_, v_m_422_, v_n_423_);
lean_dec(v_n_423_);
lean_dec(v_m_422_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(lean_object* v_00_u03b2_426_, lean_object* v_k_427_, lean_object* v_t_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_k_427_, v_t_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___boxed(lean_object* v_00_u03b2_430_, lean_object* v_k_431_, lean_object* v_t_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0(v_00_u03b2_430_, v_k_431_, v_t_432_);
lean_dec(v_t_432_);
lean_dec(v_k_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object* v_t_435_, lean_object* v_k_436_){
_start:
{
if (lean_obj_tag(v_t_435_) == 0)
{
lean_object* v_k_437_; lean_object* v_v_438_; lean_object* v_l_439_; lean_object* v_r_440_; uint8_t v___x_441_; 
v_k_437_ = lean_ctor_get(v_t_435_, 1);
v_v_438_ = lean_ctor_get(v_t_435_, 2);
v_l_439_ = lean_ctor_get(v_t_435_, 3);
v_r_440_ = lean_ctor_get(v_t_435_, 4);
v___x_441_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_436_, v_k_437_);
switch(v___x_441_)
{
case 0:
{
v_t_435_ = v_l_439_;
goto _start;
}
case 1:
{
lean_object* v___x_443_; 
lean_inc(v_v_438_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_v_438_);
return v___x_443_;
}
default: 
{
v_t_435_ = v_r_440_;
goto _start;
}
}
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_box(0);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg___boxed(lean_object* v_t_446_, lean_object* v_k_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_446_, v_k_447_);
lean_dec(v_k_447_);
lean_dec(v_t_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg(lean_object* v_m_449_, lean_object* v_n_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_449_, v_n_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___redArg___boxed(lean_object* v_m_452_, lean_object* v_n_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_NameMap_find_x3f___redArg(v_m_452_, v_n_453_);
lean_dec(v_n_453_);
lean_dec(v_m_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f(lean_object* v_00_u03b1_455_, lean_object* v_m_456_, lean_object* v_n_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_m_456_, v_n_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_find_x3f___boxed(lean_object* v_00_u03b1_459_, lean_object* v_m_460_, lean_object* v_n_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_NameMap_find_x3f(v_00_u03b1_459_, v_m_460_, v_n_461_);
lean_dec(v_n_461_);
lean_dec(v_m_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(lean_object* v_00_u03b4_463_, lean_object* v_t_464_, lean_object* v_k_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_t_464_, v_k_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b4_467_, lean_object* v_t_468_, lean_object* v_k_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0(v_00_u03b4_467_, v_t_468_, v_k_469_);
lean_dec(v_k_469_);
lean_dec(v_t_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg___lam__0(lean_object* v_e_471_, lean_object* v_s_472_){
_start:
{
lean_object* v_fst_473_; lean_object* v_snd_474_; lean_object* v___x_475_; 
v_fst_473_ = lean_ctor_get(v_e_471_, 0);
lean_inc(v_fst_473_);
v_snd_474_ = lean_ctor_get(v_e_471_, 1);
lean_inc(v_snd_474_);
lean_dec_ref(v_e_471_);
v___x_475_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_473_, v_snd_474_, v_s_472_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg(){
_start:
{
lean_object* v___f_478_; 
v___f_478_ = ((lean_object*)(l_Lean_NameMap_instInsertProdName___redArg___closed__0));
return v___f_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName___redArg___boxed(lean_object* v___dummy_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_NameMap_instInsertProdName___redArg();
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instInsertProdName(lean_object* v_00_u03b1_481_){
_start:
{
lean_object* v___f_482_; 
v___f_482_ = ((lean_object*)(l_Lean_NameMap_instInsertProdName___redArg___closed__0));
return v___f_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_483_, lean_object* v_a_484_, lean_object* v_b_485_, lean_object* v_c_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_a_484_);
lean_ctor_set(v___x_487_, 1, v_b_485_);
v___x_488_ = lean_apply_2(v_f_483_, v___x_487_, v_c_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_489_, lean_object* v_____do__lift_490_){
_start:
{
lean_object* v_a_491_; lean_object* v___x_492_; 
v_a_491_ = lean_ctor_get(v_____do__lift_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v_____do__lift_490_);
v___x_492_ = lean_apply_2(v_toPure_489_, lean_box(0), v_a_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg(lean_object* v_inst_493_, lean_object* v_m_494_, lean_object* v_init_495_, lean_object* v_f_496_){
_start:
{
lean_object* v_toApplicative_497_; lean_object* v_toBind_498_; lean_object* v_toPure_499_; lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___f_502_; lean_object* v___x_503_; 
v_toApplicative_497_ = lean_ctor_get(v_inst_493_, 0);
v_toBind_498_ = lean_ctor_get(v_inst_493_, 1);
lean_inc(v_toBind_498_);
v_toPure_499_ = lean_ctor_get(v_toApplicative_497_, 1);
lean_inc(v_toPure_499_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_500_, 0, v_f_496_);
v___x_501_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_493_, v___f_500_, v_init_495_, v_m_494_);
v___f_502_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_502_, 0, v_toPure_499_);
v___x_503_ = lean_apply_4(v_toBind_498_, lean_box(0), lean_box(0), v___x_501_, v___f_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1(lean_object* v_00_u03b1_504_, lean_object* v_m_505_, lean_object* v_inst_506_, lean_object* v_00_u03b2_507_, lean_object* v_m_508_, lean_object* v_init_509_, lean_object* v_f_510_){
_start:
{
lean_object* v_toApplicative_511_; lean_object* v_toBind_512_; lean_object* v_toPure_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v_toApplicative_511_ = lean_ctor_get(v_inst_506_, 0);
v_toBind_512_ = lean_ctor_get(v_inst_506_, 1);
lean_inc(v_toBind_512_);
v_toPure_513_ = lean_ctor_get(v_toApplicative_511_, 1);
lean_inc(v_toPure_513_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_514_, 0, v_f_510_);
v___x_515_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_506_, v___f_514_, v_init_509_, v_m_508_);
v___f_516_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_516_, 0, v_toPure_513_);
v___x_517_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_515_, v___f_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___redArg(lean_object* v_inst_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_519_, 0, lean_box(0));
lean_closure_set(v___x_519_, 1, lean_box(0));
lean_closure_set(v___x_519_, 2, v_inst_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad(lean_object* v_00_u03b1_520_, lean_object* v_m_521_, lean_object* v_inst_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_523_, 0, lean_box(0));
lean_closure_set(v___x_523_, 1, lean_box(0));
lean_closure_set(v___x_523_, 2, v_inst_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object* v_f_524_, lean_object* v_t_525_){
_start:
{
if (lean_obj_tag(v_t_525_) == 0)
{
lean_object* v_k_526_; lean_object* v_v_527_; lean_object* v_l_528_; lean_object* v_r_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_k_526_ = lean_ctor_get(v_t_525_, 1);
lean_inc_n(v_k_526_, 2);
v_v_527_ = lean_ctor_get(v_t_525_, 2);
lean_inc_n(v_v_527_, 2);
v_l_528_ = lean_ctor_get(v_t_525_, 3);
lean_inc(v_l_528_);
v_r_529_ = lean_ctor_get(v_t_525_, 4);
lean_inc(v_r_529_);
lean_dec_ref_known(v_t_525_, 5);
lean_inc_ref(v_f_524_);
v___x_530_ = lean_apply_2(v_f_524_, v_k_526_, v_v_527_);
v___x_531_ = lean_unbox(v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v_impl_532_; lean_object* v_impl_533_; lean_object* v___x_534_; 
lean_dec(v_v_527_);
lean_dec(v_k_526_);
lean_inc_ref(v_f_524_);
v_impl_532_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_524_, v_l_528_);
v_impl_533_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_524_, v_r_529_);
v___x_534_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_532_, v_impl_533_);
return v___x_534_;
}
else
{
lean_object* v_impl_535_; lean_object* v_impl_536_; lean_object* v___x_537_; 
lean_inc_ref(v_f_524_);
v_impl_535_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_524_, v_l_528_);
v_impl_536_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_524_, v_r_529_);
v___x_537_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_526_, v_v_527_, v_impl_535_, v_impl_536_);
return v___x_537_;
}
}
else
{
lean_dec_ref(v_f_524_);
return v_t_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object* v_f_538_, lean_object* v_m_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_538_, v_m_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object* v_00_u03b1_541_, lean_object* v_f_542_, lean_object* v_m_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_542_, v_m_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(lean_object* v_00_u03b1_545_, lean_object* v_f_546_, lean_object* v_t_547_, lean_object* v_hl_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_546_, v_t_547_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_NameSet_empty(void){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_box(1);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_NameSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_box(1);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_NameSet_instInhabited(void){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = lean_box(1);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object* v_s_553_, lean_object* v_n_554_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_554_, v_s_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_554_, v___x_556_, v_s_553_);
return v___x_557_;
}
else
{
lean_dec(v_n_554_);
return v_s_553_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object* v_s_558_, lean_object* v_n_559_){
_start:
{
uint8_t v___x_560_; 
v___x_560_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_559_, v_s_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object* v_s_561_, lean_object* v_n_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l_Lean_NameSet_contains(v_s_561_, v_n_562_);
lean_dec(v_n_562_);
lean_dec(v_s_561_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInsertName___lam__0(lean_object* v_n_565_, lean_object* v_s_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_NameSet_insert(v_s_566_, v_n_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_570_, lean_object* v_a_571_, lean_object* v_b_572_, lean_object* v_c_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_apply_2(v_f_570_, v_a_571_, v_c_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg(lean_object* v_inst_575_, lean_object* v_m_576_, lean_object* v_init_577_, lean_object* v_f_578_){
_start:
{
lean_object* v_toApplicative_579_; lean_object* v_toBind_580_; lean_object* v_toPure_581_; lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v_toApplicative_579_ = lean_ctor_get(v_inst_575_, 0);
v_toBind_580_ = lean_ctor_get(v_inst_575_, 1);
lean_inc(v_toBind_580_);
v_toPure_581_ = lean_ctor_get(v_toApplicative_579_, 1);
lean_inc(v_toPure_581_);
v___f_582_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_582_, 0, v_f_578_);
v___x_583_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_575_, v___f_582_, v_init_577_, v_m_576_);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_584_, 0, v_toPure_581_);
v___x_585_ = lean_apply_4(v_toBind_580_, lean_box(0), lean_box(0), v___x_583_, v___f_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1(lean_object* v_m_586_, lean_object* v_inst_587_, lean_object* v_00_u03b2_588_, lean_object* v_m_589_, lean_object* v_init_590_, lean_object* v_f_591_){
_start:
{
lean_object* v_toApplicative_592_; lean_object* v_toBind_593_; lean_object* v_toPure_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___f_597_; lean_object* v___x_598_; 
v_toApplicative_592_ = lean_ctor_get(v_inst_587_, 0);
v_toBind_593_ = lean_ctor_get(v_inst_587_, 1);
lean_inc(v_toBind_593_);
v_toPure_594_ = lean_ctor_get(v_toApplicative_592_, 1);
lean_inc(v_toPure_594_);
v___f_595_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_595_, 0, v_f_591_);
v___x_596_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_587_, v___f_595_, v_init_590_, v_m_589_);
v___f_597_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_597_, 0, v_toPure_594_);
v___x_598_ = lean_apply_4(v_toBind_593_, lean_box(0), lean_box(0), v___x_596_, v___f_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___redArg(lean_object* v_inst_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_600_, 0, lean_box(0));
lean_closure_set(v___x_600_, 1, v_inst_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad(lean_object* v_m_601_, lean_object* v_inst_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_603_, 0, lean_box(0));
lean_closure_set(v___x_603_, 1, v_inst_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_b_u2082_606_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0));
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_610_, lean_object* v_x_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_610_, v_x_611_);
lean_dec(v_x_611_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(lean_object* v_b_u2082_613_, lean_object* v_k_614_, lean_object* v_t_615_){
_start:
{
if (lean_obj_tag(v_t_615_) == 0)
{
lean_object* v_size_616_; lean_object* v_k_617_; lean_object* v_v_618_; lean_object* v_l_619_; lean_object* v_r_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_635_; 
v_size_616_ = lean_ctor_get(v_t_615_, 0);
v_k_617_ = lean_ctor_get(v_t_615_, 1);
v_v_618_ = lean_ctor_get(v_t_615_, 2);
v_l_619_ = lean_ctor_get(v_t_615_, 3);
v_r_620_ = lean_ctor_get(v_t_615_, 4);
v_isSharedCheck_635_ = !lean_is_exclusive(v_t_615_);
if (v_isSharedCheck_635_ == 0)
{
v___x_622_ = v_t_615_;
v_isShared_623_ = v_isSharedCheck_635_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_r_620_);
lean_inc(v_l_619_);
lean_inc(v_v_618_);
lean_inc(v_k_617_);
lean_inc(v_size_616_);
lean_dec(v_t_615_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_635_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint8_t v___x_624_; 
v___x_624_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_614_, v_k_617_);
switch(v___x_624_)
{
case 0:
{
lean_object* v_impl_625_; lean_object* v___x_626_; 
lean_del_object(v___x_622_);
lean_dec(v_size_616_);
v_impl_625_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_613_, v_k_614_, v_l_619_);
v___x_626_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_617_, v_v_618_, v_impl_625_, v_r_620_);
return v___x_626_;
}
case 1:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_val_629_; lean_object* v___x_631_; 
lean_dec(v_k_617_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_v_618_);
v___x_628_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_613_, v___x_627_);
lean_dec_ref_known(v___x_627_, 1);
v_val_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_629_);
lean_dec(v___x_628_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 2, v_val_629_);
lean_ctor_set(v___x_622_, 1, v_k_614_);
v___x_631_ = v___x_622_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_size_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_614_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_val_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_l_619_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_r_620_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
default: 
{
lean_object* v_impl_633_; lean_object* v___x_634_; 
lean_del_object(v___x_622_);
lean_dec(v_size_616_);
v_impl_633_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_613_, v_k_614_, v_r_620_);
v___x_634_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_617_, v_v_618_, v_l_619_, v_impl_633_);
return v___x_634_;
}
}
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_val_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_636_ = lean_box(0);
v___x_637_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_613_, v___x_636_);
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec(v___x_637_);
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_k_614_);
lean_ctor_set(v___x_640_, 2, v_val_638_);
lean_ctor_set(v___x_640_, 3, v_t_615_);
lean_ctor_set(v___x_640_, 4, v_t_615_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(lean_object* v_init_641_, lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v_k_643_; lean_object* v_v_644_; lean_object* v_l_645_; lean_object* v_r_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_k_643_ = lean_ctor_get(v_x_642_, 1);
lean_inc(v_k_643_);
v_v_644_ = lean_ctor_get(v_x_642_, 2);
lean_inc(v_v_644_);
v_l_645_ = lean_ctor_get(v_x_642_, 3);
lean_inc(v_l_645_);
v_r_646_ = lean_ctor_get(v_x_642_, 4);
lean_inc(v_r_646_);
lean_dec_ref_known(v_x_642_, 5);
v___x_647_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_641_, v_l_645_);
v___x_648_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_v_644_, v_k_643_, v___x_647_);
v_init_641_ = v___x_648_;
v_x_642_ = v_r_646_;
goto _start;
}
else
{
return v_init_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object* v_s_650_, lean_object* v_t_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_s_650_, v_t_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(lean_object* v_b_u2082_653_, lean_object* v_k_654_, lean_object* v_t_655_, lean_object* v_hl_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_653_, v_k_654_, v_t_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(lean_object* v_init_658_, lean_object* v_t_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_658_, v_t_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSingletonName___lam__0(lean_object* v_n_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_box(1);
v___x_665_ = l_Lean_NameSet_insert(v___x_664_, v_n_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0(lean_object* v_t_669_, lean_object* v_c_670_, lean_object* v_a_671_, lean_object* v_x_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_a_671_, v_t_669_);
if (v___x_673_ == 0)
{
lean_dec(v_a_671_);
return v_c_670_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_NameSet_insert(v_c_670_, v_a_671_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0___boxed(lean_object* v_t_675_, lean_object* v_c_676_, lean_object* v_a_677_, lean_object* v_x_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_NameSet_instInter___lam__0(v_t_675_, v_c_676_, v_a_677_, v_x_678_);
lean_dec(v_t_675_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__1(lean_object* v_s_680_, lean_object* v_t_681_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___f_682_ = lean_alloc_closure((void*)(l_Lean_NameSet_instInter___lam__0___boxed), 4, 1);
lean_closure_set(v___f_682_, 0, v_t_681_);
v___x_683_ = lean_box(1);
v___x_684_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_682_, v___x_683_, v_s_680_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__0(lean_object* v___x_687_, lean_object* v_c_688_, lean_object* v_a_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_687_, v_a_689_, v_c_688_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__1(lean_object* v_s_695_, lean_object* v_t_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
v___f_697_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__1));
v___x_698_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_697_, v_s_695_, v_t_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(lean_object* v_f_701_, lean_object* v_t_702_){
_start:
{
if (lean_obj_tag(v_t_702_) == 0)
{
lean_object* v_k_703_; lean_object* v_v_704_; lean_object* v_l_705_; lean_object* v_r_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_k_703_ = lean_ctor_get(v_t_702_, 1);
lean_inc_n(v_k_703_, 2);
v_v_704_ = lean_ctor_get(v_t_702_, 2);
lean_inc(v_v_704_);
v_l_705_ = lean_ctor_get(v_t_702_, 3);
lean_inc(v_l_705_);
v_r_706_ = lean_ctor_get(v_t_702_, 4);
lean_inc(v_r_706_);
lean_dec_ref_known(v_t_702_, 5);
lean_inc_ref(v_f_701_);
v___x_707_ = lean_apply_1(v_f_701_, v_k_703_);
v___x_708_ = lean_unbox(v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v_impl_709_; lean_object* v_impl_710_; lean_object* v___x_711_; 
lean_dec(v_v_704_);
lean_dec(v_k_703_);
lean_inc_ref(v_f_701_);
v_impl_709_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_701_, v_l_705_);
v_impl_710_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_701_, v_r_706_);
v___x_711_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_709_, v_impl_710_);
return v___x_711_;
}
else
{
lean_object* v_impl_712_; lean_object* v_impl_713_; lean_object* v___x_714_; 
lean_inc_ref(v_f_701_);
v_impl_712_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_701_, v_l_705_);
v_impl_713_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_701_, v_r_706_);
v___x_714_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_703_, v_v_704_, v_impl_712_, v_impl_713_);
return v___x_714_;
}
}
else
{
lean_dec_ref(v_f_701_);
return v_t_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object* v_f_715_, lean_object* v_s_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_715_, v_s_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(lean_object* v_f_718_, lean_object* v_t_719_, lean_object* v_hl_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_718_, v_t_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList(lean_object* v_l_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_724_ = l_Std_TreeSet_ofList___redArg(v_l_722_, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList___boxed(lean_object* v_l_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_NameSet_ofList(v_l_725_);
lean_dec(v_l_725_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray(lean_object* v_l_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_729_ = l_Std_TreeSet_ofArray___redArg(v_l_727_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray___boxed(lean_object* v_l_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_NameSet_ofArray(v_l_730_);
lean_dec_ref(v_l_730_);
return v_res_731_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__0(void){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_SMap_empty___redArg();
return v___x_732_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__0, &l_Lean_NameSSet_empty___closed__0_once, _init_l_Lean_NameSSet_empty___closed__0);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_NameSSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__0, &l_Lean_NameSSet_empty___closed__0_once, _init_l_Lean_NameSSet_empty___closed__0);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_NameSSet_instInhabited(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__0, &l_Lean_NameSSet_empty___closed__0_once, _init_l_Lean_NameSSet_empty___closed__0);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object* v_s_738_, lean_object* v_n_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__0));
v___x_741_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__1));
v___x_742_ = lean_box(0);
v___x_743_ = l_Lean_SMap_insert___redArg(v___x_740_, v___x_741_, v_s_738_, v_n_739_, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object* v_s_744_, lean_object* v_n_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_746_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__0));
v___x_747_ = ((lean_object*)(l_Lean_NameSSet_insert___closed__1));
v___x_748_ = l_Lean_SMap_contains___redArg(v___x_746_, v___x_747_, v_s_744_, v_n_745_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object* v_s_749_, lean_object* v_n_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Lean_NameSSet_contains(v_s_749_, v_n_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__0(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_box(0);
v___x_754_ = lean_unsigned_to_nat(16u);
v___x_755_ = lean_mk_array(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__0, &l_Lean_NameHashSet_empty___closed__0_once, _init_l_Lean_NameHashSet_empty___closed__0);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty(void){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instInhabited(void){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_761_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object* v_a_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
uint8_t v___x_764_; 
v___x_764_ = 0;
return v___x_764_;
}
else
{
lean_object* v_key_765_; lean_object* v_tail_766_; uint8_t v___x_767_; 
v_key_765_ = lean_ctor_get(v_x_763_, 0);
v_tail_766_ = lean_ctor_get(v_x_763_, 2);
v___x_767_ = lean_name_eq(v_key_765_, v_a_762_);
if (v___x_767_ == 0)
{
v_x_763_ = v_tail_766_;
goto _start;
}
else
{
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_769_, lean_object* v_x_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_769_, v_x_770_);
lean_dec(v_x_770_);
lean_dec(v_a_769_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
return v_x_773_;
}
else
{
lean_object* v_key_775_; lean_object* v_value_776_; lean_object* v_tail_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_803_; 
v_key_775_ = lean_ctor_get(v_x_774_, 0);
v_value_776_ = lean_ctor_get(v_x_774_, 1);
v_tail_777_ = lean_ctor_get(v_x_774_, 2);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_803_ == 0)
{
v___x_779_ = v_x_774_;
v_isShared_780_ = v_isSharedCheck_803_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_tail_777_);
lean_inc(v_value_776_);
lean_inc(v_key_775_);
lean_dec(v_x_774_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_803_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; uint64_t v___y_783_; 
v___x_781_ = lean_array_get_size(v_x_773_);
if (lean_obj_tag(v_key_775_) == 0)
{
uint64_t v___x_801_; 
v___x_801_ = 1723ULL;
v___y_783_ = v___x_801_;
goto v___jp_782_;
}
else
{
uint64_t v_hash_802_; 
v_hash_802_ = lean_ctor_get_uint64(v_key_775_, sizeof(void*)*2);
v___y_783_ = v_hash_802_;
goto v___jp_782_;
}
v___jp_782_:
{
uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v_fold_786_; uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_784_ = 32ULL;
v___x_785_ = lean_uint64_shift_right(v___y_783_, v___x_784_);
v_fold_786_ = lean_uint64_xor(v___y_783_, v___x_785_);
v___x_787_ = 16ULL;
v___x_788_ = lean_uint64_shift_right(v_fold_786_, v___x_787_);
v___x_789_ = lean_uint64_xor(v_fold_786_, v___x_788_);
v___x_790_ = lean_uint64_to_usize(v___x_789_);
v___x_791_ = lean_usize_of_nat(v___x_781_);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_sub(v___x_791_, v___x_792_);
v___x_794_ = lean_usize_land(v___x_790_, v___x_793_);
v___x_795_ = lean_array_uget_borrowed(v_x_773_, v___x_794_);
lean_inc(v___x_795_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 2, v___x_795_);
v___x_797_ = v___x_779_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_key_775_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_value_776_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v___x_795_);
v___x_797_ = v_reuseFailAlloc_800_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_array_uset(v_x_773_, v___x_794_, v___x_797_);
v_x_773_ = v___x_798_;
v_x_774_ = v_tail_777_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_804_, lean_object* v_source_805_, lean_object* v_target_806_){
_start:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_array_get_size(v_source_805_);
v___x_808_ = lean_nat_dec_lt(v_i_804_, v___x_807_);
if (v___x_808_ == 0)
{
lean_dec_ref(v_source_805_);
lean_dec(v_i_804_);
return v_target_806_;
}
else
{
lean_object* v_es_809_; lean_object* v___x_810_; lean_object* v_source_811_; lean_object* v_target_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_es_809_ = lean_array_fget(v_source_805_, v_i_804_);
v___x_810_ = lean_box(0);
v_source_811_ = lean_array_fset(v_source_805_, v_i_804_, v___x_810_);
v_target_812_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_806_, v_es_809_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v_i_804_, v___x_813_);
lean_dec(v_i_804_);
v_i_804_ = v___x_814_;
v_source_805_ = v_source_811_;
v_target_806_ = v_target_812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(lean_object* v_data_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_nbuckets_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_817_ = lean_array_get_size(v_data_816_);
v___x_818_ = lean_unsigned_to_nat(2u);
v_nbuckets_819_ = lean_nat_mul(v___x_817_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_box(0);
v___x_822_ = lean_mk_array(v_nbuckets_819_, v___x_821_);
v___x_823_ = lean_array_propagate_mark(v_data_816_, v___x_822_);
v___x_824_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v___x_820_, v_data_816_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object* v_m_825_, lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v_size_828_; lean_object* v_buckets_829_; lean_object* v___x_830_; uint64_t v___y_832_; 
v_size_828_ = lean_ctor_get(v_m_825_, 0);
v_buckets_829_ = lean_ctor_get(v_m_825_, 1);
v___x_830_ = lean_array_get_size(v_buckets_829_);
if (lean_obj_tag(v_a_826_) == 0)
{
uint64_t v___x_869_; 
v___x_869_ = 1723ULL;
v___y_832_ = v___x_869_;
goto v___jp_831_;
}
else
{
uint64_t v_hash_870_; 
v_hash_870_ = lean_ctor_get_uint64(v_a_826_, sizeof(void*)*2);
v___y_832_ = v_hash_870_;
goto v___jp_831_;
}
v___jp_831_:
{
uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v_fold_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; size_t v___x_843_; lean_object* v_bkt_844_; uint8_t v___x_845_; 
v___x_833_ = 32ULL;
v___x_834_ = lean_uint64_shift_right(v___y_832_, v___x_833_);
v_fold_835_ = lean_uint64_xor(v___y_832_, v___x_834_);
v___x_836_ = 16ULL;
v___x_837_ = lean_uint64_shift_right(v_fold_835_, v___x_836_);
v___x_838_ = lean_uint64_xor(v_fold_835_, v___x_837_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = lean_usize_of_nat(v___x_830_);
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_sub(v___x_840_, v___x_841_);
v___x_843_ = lean_usize_land(v___x_839_, v___x_842_);
v_bkt_844_ = lean_array_uget_borrowed(v_buckets_829_, v___x_843_);
v___x_845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_826_, v_bkt_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_866_; 
lean_inc_ref(v_buckets_829_);
lean_inc(v_size_828_);
v_isSharedCheck_866_ = !lean_is_exclusive(v_m_825_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; lean_object* v_unused_868_; 
v_unused_867_ = lean_ctor_get(v_m_825_, 1);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_m_825_, 0);
lean_dec(v_unused_868_);
v___x_847_ = v_m_825_;
v_isShared_848_ = v_isSharedCheck_866_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_m_825_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_866_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v_size_x27_850_; lean_object* v___x_851_; lean_object* v_buckets_x27_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v_size_x27_850_ = lean_nat_add(v_size_828_, v___x_849_);
lean_dec(v_size_828_);
lean_inc(v_bkt_844_);
v___x_851_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_851_, 0, v_a_826_);
lean_ctor_set(v___x_851_, 1, v_b_827_);
lean_ctor_set(v___x_851_, 2, v_bkt_844_);
v_buckets_x27_852_ = lean_array_uset(v_buckets_829_, v___x_843_, v___x_851_);
v___x_853_ = lean_unsigned_to_nat(4u);
v___x_854_ = lean_nat_mul(v_size_x27_850_, v___x_853_);
v___x_855_ = lean_unsigned_to_nat(3u);
v___x_856_ = lean_nat_div(v___x_854_, v___x_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_array_get_size(v_buckets_x27_852_);
v___x_858_ = lean_nat_dec_le(v___x_856_, v___x_857_);
lean_dec(v___x_856_);
if (v___x_858_ == 0)
{
lean_object* v_val_859_; lean_object* v___x_861_; 
v_val_859_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_buckets_x27_852_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v_val_859_);
lean_ctor_set(v___x_847_, 0, v_size_x27_850_);
v___x_861_ = v___x_847_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_size_x27_850_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_val_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v___x_864_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v_buckets_x27_852_);
lean_ctor_set(v___x_847_, 0, v_size_x27_850_);
v___x_864_ = v___x_847_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_size_x27_850_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_buckets_x27_852_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_dec(v_b_827_);
lean_dec(v_a_826_);
return v_m_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object* v_s_871_, lean_object* v_n_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(0);
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_s_871_, v_n_872_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(lean_object* v_00_u03b2_875_, lean_object* v_m_876_, lean_object* v_a_877_, lean_object* v_b_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_876_, v_a_877_, v_b_878_);
return v___x_879_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_880_, lean_object* v_a_881_, lean_object* v_x_882_){
_start:
{
uint8_t v___x_883_; 
v___x_883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_881_, v_x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_884_, lean_object* v_a_885_, lean_object* v_x_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(v_00_u03b2_884_, v_a_885_, v_x_886_);
lean_dec(v_x_886_);
lean_dec(v_a_885_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(lean_object* v_00_u03b2_889_, lean_object* v_data_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_data_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_892_, lean_object* v_i_893_, lean_object* v_source_894_, lean_object* v_target_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v_i_893_, v_source_894_, v_target_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_898_, v_x_899_);
return v___x_900_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object* v_m_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_buckets_903_; lean_object* v___x_904_; uint64_t v___y_906_; 
v_buckets_903_ = lean_ctor_get(v_m_901_, 1);
v___x_904_ = lean_array_get_size(v_buckets_903_);
if (lean_obj_tag(v_a_902_) == 0)
{
uint64_t v___x_920_; 
v___x_920_ = 1723ULL;
v___y_906_ = v___x_920_;
goto v___jp_905_;
}
else
{
uint64_t v_hash_921_; 
v_hash_921_ = lean_ctor_get_uint64(v_a_902_, sizeof(void*)*2);
v___y_906_ = v_hash_921_;
goto v___jp_905_;
}
v___jp_905_:
{
uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v_fold_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_907_ = 32ULL;
v___x_908_ = lean_uint64_shift_right(v___y_906_, v___x_907_);
v_fold_909_ = lean_uint64_xor(v___y_906_, v___x_908_);
v___x_910_ = 16ULL;
v___x_911_ = lean_uint64_shift_right(v_fold_909_, v___x_910_);
v___x_912_ = lean_uint64_xor(v_fold_909_, v___x_911_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = lean_usize_of_nat(v___x_904_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_sub(v___x_914_, v___x_915_);
v___x_917_ = lean_usize_land(v___x_913_, v___x_916_);
v___x_918_ = lean_array_uget_borrowed(v_buckets_903_, v___x_917_);
v___x_919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_902_, v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object* v_m_922_, lean_object* v_a_923_){
_start:
{
uint8_t v_res_924_; lean_object* v_r_925_; 
v_res_924_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_m_922_);
v_r_925_ = lean_box(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object* v_s_926_, lean_object* v_n_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_s_926_, v_n_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object* v_s_929_, lean_object* v_n_930_){
_start:
{
uint8_t v_res_931_; lean_object* v_r_932_; 
v_res_931_ = l_Lean_NameHashSet_contains(v_s_929_, v_n_930_);
lean_dec(v_n_930_);
lean_dec_ref(v_s_929_);
v_r_932_ = lean_box(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object* v_00_u03b2_933_, lean_object* v_m_934_, lean_object* v_a_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_934_, v_a_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object* v_00_u03b2_937_, lean_object* v_m_938_, lean_object* v_a_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(v_00_u03b2_937_, v_m_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_m_938_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object* v_f_942_, lean_object* v_acc_943_, lean_object* v_a_944_){
_start:
{
if (lean_obj_tag(v_a_944_) == 0)
{
lean_dec_ref(v_f_942_);
return v_acc_943_;
}
else
{
lean_object* v_key_945_; lean_object* v_value_946_; lean_object* v_tail_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_958_; 
v_key_945_ = lean_ctor_get(v_a_944_, 0);
v_value_946_ = lean_ctor_get(v_a_944_, 1);
v_tail_947_ = lean_ctor_get(v_a_944_, 2);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_944_);
if (v_isSharedCheck_958_ == 0)
{
v___x_949_ = v_a_944_;
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_tail_947_);
lean_inc(v_value_946_);
lean_inc(v_key_945_);
lean_dec(v_a_944_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
lean_inc_ref(v_f_942_);
lean_inc(v_key_945_);
v___x_951_ = lean_apply_1(v_f_942_, v_key_945_);
v___x_952_ = lean_unbox(v___x_951_);
if (v___x_952_ == 0)
{
lean_del_object(v___x_949_);
lean_dec(v_value_946_);
lean_dec(v_key_945_);
v_a_944_ = v_tail_947_;
goto _start;
}
else
{
lean_object* v___x_955_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v_acc_943_);
v___x_955_ = v___x_949_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_key_945_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_value_946_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_acc_943_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v_acc_943_ = v___x_955_;
v_a_944_ = v_tail_947_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(lean_object* v_f_959_, size_t v_sz_960_, size_t v_i_961_, lean_object* v_bs_962_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = lean_usize_dec_lt(v_i_961_, v_sz_960_);
if (v___x_963_ == 0)
{
lean_dec_ref(v_f_959_);
return v_bs_962_;
}
else
{
lean_object* v_v_964_; lean_object* v___x_965_; lean_object* v_bs_x27_966_; lean_object* v___x_967_; lean_object* v___x_968_; size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
v_v_964_ = lean_array_uget(v_bs_962_, v_i_961_);
v___x_965_ = lean_unsigned_to_nat(0u);
v_bs_x27_966_ = lean_array_uset(v_bs_962_, v_i_961_, v___x_965_);
v___x_967_ = lean_box(0);
lean_inc_ref(v_f_959_);
v___x_968_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_959_, v___x_967_, v_v_964_);
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_961_, v___x_969_);
v___x_971_ = lean_array_uset(v_bs_x27_966_, v_i_961_, v___x_968_);
v_i_961_ = v___x_970_;
v_bs_962_ = v___x_971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(lean_object* v_f_973_, lean_object* v_sz_974_, lean_object* v_i_975_, lean_object* v_bs_976_){
_start:
{
size_t v_sz_boxed_977_; size_t v_i_boxed_978_; lean_object* v_res_979_; 
v_sz_boxed_977_ = lean_unbox_usize(v_sz_974_);
lean_dec(v_sz_974_);
v_i_boxed_978_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_973_, v_sz_boxed_977_, v_i_boxed_978_, v_bs_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(lean_object* v_as_980_, size_t v_i_981_, size_t v_stop_982_, lean_object* v_b_983_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_eq(v_i_981_, v_stop_982_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; size_t v___x_988_; size_t v___x_989_; 
v___x_985_ = lean_array_uget_borrowed(v_as_980_, v_i_981_);
v___x_986_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_985_);
v___x_987_ = lean_nat_add(v_b_983_, v___x_986_);
lean_dec(v___x_986_);
lean_dec(v_b_983_);
v___x_988_ = ((size_t)1ULL);
v___x_989_ = lean_usize_add(v_i_981_, v___x_988_);
v_i_981_ = v___x_989_;
v_b_983_ = v___x_987_;
goto _start;
}
else
{
return v_b_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(lean_object* v_as_991_, lean_object* v_i_992_, lean_object* v_stop_993_, lean_object* v_b_994_){
_start:
{
size_t v_i_boxed_995_; size_t v_stop_boxed_996_; lean_object* v_res_997_; 
v_i_boxed_995_ = lean_unbox_usize(v_i_992_);
lean_dec(v_i_992_);
v_stop_boxed_996_ = lean_unbox_usize(v_stop_993_);
lean_dec(v_stop_993_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_as_991_, v_i_boxed_995_, v_stop_boxed_996_, v_b_994_);
lean_dec_ref(v_as_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object* v_f_998_, lean_object* v_m_999_){
_start:
{
lean_object* v_buckets_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1018_; 
v_buckets_1000_ = lean_ctor_get(v_m_999_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_m_999_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_m_999_, 0);
lean_dec(v_unused_1019_);
v___x_1002_ = v_m_999_;
v_isShared_1003_ = v_isSharedCheck_1018_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_buckets_1000_);
lean_dec(v_m_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1018_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
size_t v_sz_1004_; size_t v___x_1005_; lean_object* v_newBuckets_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_sz_1004_ = lean_array_size(v_buckets_1000_);
v___x_1005_ = ((size_t)0ULL);
v_newBuckets_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_998_, v_sz_1004_, v___x_1005_, v_buckets_1000_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_array_get_size(v_newBuckets_1006_);
v___x_1009_ = lean_nat_dec_lt(v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1011_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v_newBuckets_1006_);
lean_ctor_set(v___x_1002_, 0, v___x_1007_);
v___x_1011_ = v___x_1002_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_newBuckets_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
size_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1013_ = lean_usize_of_nat(v___x_1008_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_1006_, v___x_1005_, v___x_1013_, v___x_1007_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v_newBuckets_1006_);
lean_ctor_set(v___x_1002_, 0, v___x_1014_);
v___x_1016_ = v___x_1002_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_newBuckets_1006_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object* v_f_1020_, lean_object* v_s_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(v_f_1020_, v_s_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1023_) == 0)
{
if (lean_obj_tag(v_x_1024_) == 0)
{
uint8_t v___x_1025_; 
v___x_1025_ = 1;
return v___x_1025_;
}
else
{
uint8_t v___x_1026_; 
v___x_1026_ = 0;
return v___x_1026_;
}
}
else
{
if (lean_obj_tag(v_x_1024_) == 0)
{
uint8_t v___x_1027_; 
v___x_1027_ = 0;
return v___x_1027_;
}
else
{
lean_object* v_head_1028_; lean_object* v_tail_1029_; lean_object* v_head_1030_; lean_object* v_tail_1031_; uint8_t v___x_1032_; 
v_head_1028_ = lean_ctor_get(v_x_1023_, 0);
v_tail_1029_ = lean_ctor_get(v_x_1023_, 1);
v_head_1030_ = lean_ctor_get(v_x_1024_, 0);
v_tail_1031_ = lean_ctor_get(v_x_1024_, 1);
v___x_1032_ = lean_nat_dec_eq(v_head_1028_, v_head_1030_);
if (v___x_1032_ == 0)
{
return v___x_1032_;
}
else
{
v_x_1023_ = v_tail_1029_;
v_x_1024_ = v_tail_1031_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_1034_, v_x_1035_);
lean_dec(v_x_1035_);
lean_dec(v_x_1034_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object* v_v_u2081_1038_, lean_object* v_v_u2082_1039_){
_start:
{
lean_object* v_name_1040_; lean_object* v_imported_1041_; lean_object* v_ctx_1042_; lean_object* v_scopes_1043_; lean_object* v_name_1044_; lean_object* v_imported_1045_; lean_object* v_ctx_1046_; lean_object* v_scopes_1047_; uint8_t v___y_1049_; uint8_t v___x_1052_; 
v_name_1040_ = lean_ctor_get(v_v_u2081_1038_, 0);
v_imported_1041_ = lean_ctor_get(v_v_u2081_1038_, 1);
v_ctx_1042_ = lean_ctor_get(v_v_u2081_1038_, 2);
v_scopes_1043_ = lean_ctor_get(v_v_u2081_1038_, 3);
v_name_1044_ = lean_ctor_get(v_v_u2082_1039_, 0);
v_imported_1045_ = lean_ctor_get(v_v_u2082_1039_, 1);
v_ctx_1046_ = lean_ctor_get(v_v_u2082_1039_, 2);
v_scopes_1047_ = lean_ctor_get(v_v_u2082_1039_, 3);
v___x_1052_ = l_Lean_Name_isPrefixOf(v_name_1040_, v_name_1044_);
if (v___x_1052_ == 0)
{
v___y_1049_ = v___x_1052_;
goto v___jp_1048_;
}
else
{
uint8_t v___x_1053_; 
v___x_1053_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1043_, v_scopes_1047_);
v___y_1049_ = v___x_1053_;
goto v___jp_1048_;
}
v___jp_1048_:
{
if (v___y_1049_ == 0)
{
return v___y_1049_;
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_name_eq(v_ctx_1042_, v_ctx_1046_);
if (v___x_1050_ == 0)
{
return v___x_1050_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_name_eq(v_imported_1041_, v_imported_1045_);
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object* v_v_u2081_1054_, lean_object* v_v_u2082_1055_){
_start:
{
uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_1054_, v_v_u2082_1055_);
lean_dec_ref(v_v_u2082_1055_);
lean_dec_ref(v_v_u2081_1054_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object* v_v_u2081_1058_, lean_object* v_v_u2082_1059_){
_start:
{
lean_object* v_name_1060_; lean_object* v_imported_1061_; lean_object* v_ctx_1062_; lean_object* v_scopes_1063_; lean_object* v_name_1064_; lean_object* v_imported_1065_; lean_object* v_ctx_1066_; lean_object* v_scopes_1067_; uint8_t v___y_1069_; uint8_t v___x_1072_; 
v_name_1060_ = lean_ctor_get(v_v_u2081_1058_, 0);
v_imported_1061_ = lean_ctor_get(v_v_u2081_1058_, 1);
v_ctx_1062_ = lean_ctor_get(v_v_u2081_1058_, 2);
v_scopes_1063_ = lean_ctor_get(v_v_u2081_1058_, 3);
v_name_1064_ = lean_ctor_get(v_v_u2082_1059_, 0);
v_imported_1065_ = lean_ctor_get(v_v_u2082_1059_, 1);
v_ctx_1066_ = lean_ctor_get(v_v_u2082_1059_, 2);
v_scopes_1067_ = lean_ctor_get(v_v_u2082_1059_, 3);
v___x_1072_ = l_Lean_Name_isSuffixOf(v_name_1060_, v_name_1064_);
if (v___x_1072_ == 0)
{
v___y_1069_ = v___x_1072_;
goto v___jp_1068_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1063_, v_scopes_1067_);
v___y_1069_ = v___x_1073_;
goto v___jp_1068_;
}
v___jp_1068_:
{
if (v___y_1069_ == 0)
{
return v___y_1069_;
}
else
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_name_eq(v_ctx_1062_, v_ctx_1066_);
if (v___x_1070_ == 0)
{
return v___x_1070_;
}
else
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_name_eq(v_imported_1061_, v_imported_1065_);
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object* v_v_u2081_1074_, lean_object* v_v_u2082_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_1074_, v_v_u2082_1075_);
lean_dec_ref(v_v_u2082_1075_);
lean_dec_ref(v_v_u2081_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
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
