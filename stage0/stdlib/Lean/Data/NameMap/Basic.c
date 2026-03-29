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
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofArray___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_459_, lean_object* v_a_460_, lean_object* v_b_461_, lean_object* v_c_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_a_460_);
lean_ctor_set(v___x_463_, 1, v_b_461_);
v___x_464_ = lean_apply_2(v_f_459_, v___x_463_, v_c_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_465_, lean_object* v_____do__lift_466_){
_start:
{
lean_object* v_a_467_; lean_object* v___x_468_; 
v_a_467_ = lean_ctor_get(v_____do__lift_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref(v_____do__lift_466_);
v___x_468_ = lean_apply_2(v_toPure_465_, lean_box(0), v_a_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg(lean_object* v_inst_469_, lean_object* v_m_470_, lean_object* v_init_471_, lean_object* v_f_472_){
_start:
{
lean_object* v_toApplicative_473_; lean_object* v_toBind_474_; lean_object* v_toPure_475_; lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___f_478_; lean_object* v___x_479_; 
v_toApplicative_473_ = lean_ctor_get(v_inst_469_, 0);
v_toBind_474_ = lean_ctor_get(v_inst_469_, 1);
lean_inc(v_toBind_474_);
v_toPure_475_ = lean_ctor_get(v_toApplicative_473_, 1);
lean_inc(v_toPure_475_);
v___f_476_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_476_, 0, v_f_472_);
v___x_477_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_469_, v___f_476_, v_init_471_, v_m_470_);
v___f_478_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_478_, 0, v_toPure_475_);
v___x_479_ = lean_apply_4(v_toBind_474_, lean_box(0), lean_box(0), v___x_477_, v___f_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___aux__1(lean_object* v_00_u03b1_480_, lean_object* v_m_481_, lean_object* v_inst_482_, lean_object* v_00_u03b2_483_, lean_object* v_m_484_, lean_object* v_init_485_, lean_object* v_f_486_){
_start:
{
lean_object* v_toApplicative_487_; lean_object* v_toBind_488_; lean_object* v_toPure_489_; lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___f_492_; lean_object* v___x_493_; 
v_toApplicative_487_ = lean_ctor_get(v_inst_482_, 0);
v_toBind_488_ = lean_ctor_get(v_inst_482_, 1);
lean_inc(v_toBind_488_);
v_toPure_489_ = lean_ctor_get(v_toApplicative_487_, 1);
lean_inc(v_toPure_489_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_490_, 0, v_f_486_);
v___x_491_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_482_, v___f_490_, v_init_485_, v_m_484_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_492_, 0, v_toPure_489_);
v___x_493_ = lean_apply_4(v_toBind_488_, lean_box(0), lean_box(0), v___x_491_, v___f_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad___redArg(lean_object* v_inst_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_495_, 0, lean_box(0));
lean_closure_set(v___x_495_, 1, lean_box(0));
lean_closure_set(v___x_495_, 2, v_inst_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_instForInProdNameOfMonad(lean_object* v_00_u03b1_496_, lean_object* v_m_497_, lean_object* v_inst_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_499_, 0, lean_box(0));
lean_closure_set(v___x_499_, 1, lean_box(0));
lean_closure_set(v___x_499_, 2, v_inst_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object* v_f_500_, lean_object* v_t_501_){
_start:
{
if (lean_obj_tag(v_t_501_) == 0)
{
lean_object* v_k_502_; lean_object* v_v_503_; lean_object* v_l_504_; lean_object* v_r_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_k_502_ = lean_ctor_get(v_t_501_, 1);
lean_inc_n(v_k_502_, 2);
v_v_503_ = lean_ctor_get(v_t_501_, 2);
lean_inc_n(v_v_503_, 2);
v_l_504_ = lean_ctor_get(v_t_501_, 3);
lean_inc(v_l_504_);
v_r_505_ = lean_ctor_get(v_t_501_, 4);
lean_inc(v_r_505_);
lean_dec_ref(v_t_501_);
lean_inc_ref(v_f_500_);
v___x_506_ = lean_apply_2(v_f_500_, v_k_502_, v_v_503_);
v___x_507_ = lean_unbox(v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v_impl_508_; lean_object* v_impl_509_; lean_object* v___x_510_; 
lean_dec(v_v_503_);
lean_dec(v_k_502_);
lean_inc_ref(v_f_500_);
v_impl_508_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_500_, v_l_504_);
v_impl_509_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_500_, v_r_505_);
v___x_510_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_508_, v_impl_509_);
return v___x_510_;
}
else
{
lean_object* v_impl_511_; lean_object* v_impl_512_; lean_object* v___x_513_; 
lean_inc_ref(v_f_500_);
v_impl_511_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_500_, v_l_504_);
v_impl_512_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_500_, v_r_505_);
v___x_513_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_502_, v_v_503_, v_impl_511_, v_impl_512_);
return v___x_513_;
}
}
else
{
lean_dec_ref(v_f_500_);
return v_t_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter___redArg(lean_object* v_f_514_, lean_object* v_m_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_514_, v_m_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filter(lean_object* v_00_u03b1_517_, lean_object* v_f_518_, lean_object* v_m_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_518_, v_m_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0(lean_object* v_00_u03b1_521_, lean_object* v_f_522_, lean_object* v_t_523_, lean_object* v_hl_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v_f_522_, v_t_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_NameSet_empty(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(1);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_NameSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_box(1);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_NameSet_instInhabited(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(1);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_insert(lean_object* v_s_529_, lean_object* v_n_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_530_, v_s_529_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_box(0);
v___x_533_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_530_, v___x_532_, v_s_529_);
return v___x_533_;
}
else
{
lean_dec(v_n_530_);
return v_s_529_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_NameSet_contains(lean_object* v_s_534_, lean_object* v_n_535_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_n_535_, v_s_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_contains___boxed(lean_object* v_s_537_, lean_object* v_n_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Lean_NameSet_contains(v_s_537_, v_n_538_);
lean_dec(v_n_538_);
lean_dec(v_s_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0(lean_object* v_f_541_, lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_c_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_apply_2(v_f_541_, v_a_542_, v_c_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg(lean_object* v_inst_546_, lean_object* v_m_547_, lean_object* v_init_548_, lean_object* v_f_549_){
_start:
{
lean_object* v_toApplicative_550_; lean_object* v_toBind_551_; lean_object* v_toPure_552_; lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___f_555_; lean_object* v___x_556_; 
v_toApplicative_550_ = lean_ctor_get(v_inst_546_, 0);
v_toBind_551_ = lean_ctor_get(v_inst_546_, 1);
lean_inc(v_toBind_551_);
v_toPure_552_ = lean_ctor_get(v_toApplicative_550_, 1);
lean_inc(v_toPure_552_);
v___f_553_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_553_, 0, v_f_549_);
v___x_554_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_546_, v___f_553_, v_init_548_, v_m_547_);
v___f_555_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_555_, 0, v_toPure_552_);
v___x_556_ = lean_apply_4(v_toBind_551_, lean_box(0), lean_box(0), v___x_554_, v___f_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___aux__1(lean_object* v_m_557_, lean_object* v_inst_558_, lean_object* v_00_u03b2_559_, lean_object* v_m_560_, lean_object* v_init_561_, lean_object* v_f_562_){
_start:
{
lean_object* v_toApplicative_563_; lean_object* v_toBind_564_; lean_object* v_toPure_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___f_568_; lean_object* v___x_569_; 
v_toApplicative_563_ = lean_ctor_get(v_inst_558_, 0);
v_toBind_564_ = lean_ctor_get(v_inst_558_, 1);
lean_inc(v_toBind_564_);
v_toPure_565_ = lean_ctor_get(v_toApplicative_563_, 1);
lean_inc(v_toPure_565_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_566_, 0, v_f_562_);
v___x_567_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_558_, v___f_566_, v_init_561_, v_m_560_);
v___f_568_ = lean_alloc_closure((void*)(l_Lean_NameMap_instForInProdNameOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_568_, 0, v_toPure_565_);
v___x_569_ = lean_apply_4(v_toBind_564_, lean_box(0), lean_box(0), v___x_567_, v___f_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad___redArg(lean_object* v_inst_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_571_, 0, lean_box(0));
lean_closure_set(v___x_571_, 1, v_inst_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instForInNameOfMonad(lean_object* v_m_572_, lean_object* v_inst_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_closure((void*)(l_Lean_NameSet_instForInNameOfMonad___aux__1), 6, 2);
lean_closure_set(v___x_574_, 0, lean_box(0));
lean_closure_set(v___x_574_, 1, v_inst_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v___x_579_; 
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v_b_u2082_577_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
v___x_580_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___closed__0));
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_581_, v_x_582_);
lean_dec(v_x_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(lean_object* v_b_u2082_584_, lean_object* v_k_585_, lean_object* v_t_586_){
_start:
{
if (lean_obj_tag(v_t_586_) == 0)
{
lean_object* v_size_587_; lean_object* v_k_588_; lean_object* v_v_589_; lean_object* v_l_590_; lean_object* v_r_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_606_; 
v_size_587_ = lean_ctor_get(v_t_586_, 0);
v_k_588_ = lean_ctor_get(v_t_586_, 1);
v_v_589_ = lean_ctor_get(v_t_586_, 2);
v_l_590_ = lean_ctor_get(v_t_586_, 3);
v_r_591_ = lean_ctor_get(v_t_586_, 4);
v_isSharedCheck_606_ = !lean_is_exclusive(v_t_586_);
if (v_isSharedCheck_606_ == 0)
{
v___x_593_ = v_t_586_;
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_r_591_);
lean_inc(v_l_590_);
lean_inc(v_v_589_);
lean_inc(v_k_588_);
lean_inc(v_size_587_);
lean_dec(v_t_586_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_606_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; 
v___x_595_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_585_, v_k_588_);
switch(v___x_595_)
{
case 0:
{
lean_object* v_impl_596_; lean_object* v___x_597_; 
lean_del_object(v___x_593_);
lean_dec(v_size_587_);
v_impl_596_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_584_, v_k_585_, v_l_590_);
v___x_597_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_588_, v_v_589_, v_impl_596_, v_r_591_);
return v___x_597_;
}
case 1:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_val_600_; lean_object* v___x_602_; 
lean_dec(v_k_588_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_v_589_);
v___x_599_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_584_, v___x_598_);
lean_dec_ref(v___x_598_);
v_val_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_val_600_);
lean_dec(v___x_599_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 2, v_val_600_);
lean_ctor_set(v___x_593_, 1, v_k_585_);
v___x_602_ = v___x_593_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_size_587_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_k_585_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_val_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_l_590_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v_r_591_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
default: 
{
lean_object* v_impl_604_; lean_object* v___x_605_; 
lean_del_object(v___x_593_);
lean_dec(v_size_587_);
v_impl_604_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_584_, v_k_585_, v_r_591_);
v___x_605_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_588_, v_v_589_, v_l_590_, v_impl_604_);
return v___x_605_;
}
}
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_val_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_607_ = lean_box(0);
v___x_608_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg___lam__0(v_b_u2082_584_, v___x_607_);
v_val_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_val_609_);
lean_dec(v___x_608_);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v_k_585_);
lean_ctor_set(v___x_611_, 2, v_val_609_);
lean_ctor_set(v___x_611_, 3, v_t_586_);
lean_ctor_set(v___x_611_, 4, v_t_586_);
return v___x_611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(lean_object* v_init_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v_k_614_; lean_object* v_v_615_; lean_object* v_l_616_; lean_object* v_r_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_k_614_ = lean_ctor_get(v_x_613_, 1);
lean_inc(v_k_614_);
v_v_615_ = lean_ctor_get(v_x_613_, 2);
lean_inc(v_v_615_);
v_l_616_ = lean_ctor_get(v_x_613_, 3);
lean_inc(v_l_616_);
v_r_617_ = lean_ctor_get(v_x_613_, 4);
lean_inc(v_r_617_);
lean_dec_ref(v_x_613_);
v___x_618_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_612_, v_l_616_);
v___x_619_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_v_615_, v_k_614_, v___x_618_);
v_init_612_ = v___x_619_;
v_x_613_ = v_r_617_;
goto _start;
}
else
{
return v_init_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_append(lean_object* v_s_621_, lean_object* v_t_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_s_621_, v_t_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0(lean_object* v_b_u2082_624_, lean_object* v_k_625_, lean_object* v_t_626_, lean_object* v_hl_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_NameSet_append_spec__0___redArg(v_b_u2082_624_, v_k_625_, v_t_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1(lean_object* v_init_629_, lean_object* v_t_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameSet_append_spec__1_spec__1(v_init_629_, v_t_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSingletonName___lam__0(lean_object* v_n_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_box(1);
v___x_636_ = l_Lean_NameSet_insert(v___x_635_, v_n_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0(lean_object* v_t_640_, lean_object* v_c_641_, lean_object* v_a_642_, lean_object* v_x_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_a_642_, v_t_640_);
if (v___x_644_ == 0)
{
lean_dec(v_a_642_);
return v_c_641_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_NameSet_insert(v_c_641_, v_a_642_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__0___boxed(lean_object* v_t_646_, lean_object* v_c_647_, lean_object* v_a_648_, lean_object* v_x_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_NameSet_instInter___lam__0(v_t_646_, v_c_647_, v_a_648_, v_x_649_);
lean_dec(v_t_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instInter___lam__1(lean_object* v_s_651_, lean_object* v_t_652_){
_start:
{
lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___f_653_ = lean_alloc_closure((void*)(l_Lean_NameSet_instInter___lam__0___boxed), 4, 1);
lean_closure_set(v___f_653_, 0, v_t_652_);
v___x_654_ = lean_box(1);
v___x_655_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_653_, v___x_654_, v_s_651_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__0(lean_object* v___x_658_, lean_object* v_c_659_, lean_object* v_a_660_, lean_object* v_x_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_658_, v_a_660_, v_c_659_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_instSDiff___lam__1(lean_object* v_s_666_, lean_object* v_t_667_){
_start:
{
lean_object* v___f_668_; lean_object* v___x_669_; 
v___f_668_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__1));
v___x_669_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_668_, v_s_666_, v_t_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(lean_object* v_f_672_, lean_object* v_t_673_){
_start:
{
if (lean_obj_tag(v_t_673_) == 0)
{
lean_object* v_k_674_; lean_object* v_v_675_; lean_object* v_l_676_; lean_object* v_r_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_k_674_ = lean_ctor_get(v_t_673_, 1);
lean_inc_n(v_k_674_, 2);
v_v_675_ = lean_ctor_get(v_t_673_, 2);
lean_inc(v_v_675_);
v_l_676_ = lean_ctor_get(v_t_673_, 3);
lean_inc(v_l_676_);
v_r_677_ = lean_ctor_get(v_t_673_, 4);
lean_inc(v_r_677_);
lean_dec_ref(v_t_673_);
lean_inc_ref(v_f_672_);
v___x_678_ = lean_apply_1(v_f_672_, v_k_674_);
v___x_679_ = lean_unbox(v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v_impl_680_; lean_object* v_impl_681_; lean_object* v___x_682_; 
lean_dec(v_v_675_);
lean_dec(v_k_674_);
lean_inc_ref(v_f_672_);
v_impl_680_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_672_, v_l_676_);
v_impl_681_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_672_, v_r_677_);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_link2___redArg(v_impl_680_, v_impl_681_);
return v___x_682_;
}
else
{
lean_object* v_impl_683_; lean_object* v_impl_684_; lean_object* v___x_685_; 
lean_inc_ref(v_f_672_);
v_impl_683_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_672_, v_l_676_);
v_impl_684_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_672_, v_r_677_);
v___x_685_ = l_Std_DTreeMap_Internal_Impl_link___redArg(v_k_674_, v_v_675_, v_impl_683_, v_impl_684_);
return v___x_685_;
}
}
else
{
lean_dec_ref(v_f_672_);
return v_t_673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_filter(lean_object* v_f_686_, lean_object* v_s_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_686_, v_s_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0(lean_object* v_f_689_, lean_object* v_t_690_, lean_object* v_hl_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameSet_filter_spec__0___redArg(v_f_689_, v_t_690_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofList(lean_object* v_l_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_695_ = l_Std_TreeSet_ofList___redArg(v_l_693_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray(lean_object* v_l_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_NameSet_instSDiff___lam__1___closed__0));
v___x_698_ = l_Std_TreeSet_ofArray___redArg(v_l_696_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSet_ofArray___boxed(lean_object* v_l_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_NameSet_ofArray(v_l_699_);
lean_dec_ref(v_l_699_);
return v_res_700_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty___closed__2(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_704_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_705_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v___x_704_, v___x_703_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_NameSSet_empty(void){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_NameSSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_NameSSet_instInhabited(void){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Lean_NameSSet_empty___closed__2, &l_Lean_NameSSet_empty___closed__2_once, _init_l_Lean_NameSSet_empty___closed__2);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_insert(lean_object* v_s_709_, lean_object* v_n_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_711_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_712_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_713_ = lean_box(0);
v___x_714_ = l_Lean_SMap_insert___redArg(v___x_711_, v___x_712_, v_s_709_, v_n_710_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameSSet_contains(lean_object* v_s_715_, lean_object* v_n_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__0));
v___x_718_ = ((lean_object*)(l_Lean_NameSSet_empty___closed__1));
v___x_719_ = l_Lean_SMap_contains___redArg(v___x_717_, v___x_718_, v_s_715_, v_n_716_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameSSet_contains___boxed(lean_object* v_s_720_, lean_object* v_n_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_Lean_NameSSet_contains(v_s_720_, v_n_721_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__0(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_box(0);
v___x_725_ = lean_unsigned_to_nat(16u);
v___x_726_ = lean_mk_array(v___x_725_, v___x_724_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty___closed__1(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__0, &l_Lean_NameHashSet_empty___closed__0_once, _init_l_Lean_NameHashSet_empty___closed__0);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_NameHashSet_empty(void){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instEmptyCollection(void){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_NameHashSet_instInhabited(void){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Lean_NameHashSet_empty___closed__1, &l_Lean_NameHashSet_empty___closed__1_once, _init_l_Lean_NameHashSet_empty___closed__1);
return v___x_732_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(lean_object* v_a_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
uint8_t v___x_735_; 
v___x_735_ = 0;
return v___x_735_;
}
else
{
lean_object* v_key_736_; lean_object* v_tail_737_; uint8_t v___x_738_; 
v_key_736_ = lean_ctor_get(v_x_734_, 0);
v_tail_737_ = lean_ctor_get(v_x_734_, 2);
v___x_738_ = lean_name_eq(v_key_736_, v_a_733_);
if (v___x_738_ == 0)
{
v_x_734_ = v_tail_737_;
goto _start;
}
else
{
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_740_, lean_object* v_x_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_740_, v_x_741_);
lean_dec(v_x_741_);
lean_dec(v_a_740_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_744_; uint64_t v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(1723u);
v___x_745_ = lean_uint64_of_nat(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
if (lean_obj_tag(v_x_747_) == 0)
{
return v_x_746_;
}
else
{
lean_object* v_key_748_; lean_object* v_value_749_; lean_object* v_tail_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_776_; 
v_key_748_ = lean_ctor_get(v_x_747_, 0);
v_value_749_ = lean_ctor_get(v_x_747_, 1);
v_tail_750_ = lean_ctor_get(v_x_747_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_776_ == 0)
{
v___x_752_ = v_x_747_;
v_isShared_753_ = v_isSharedCheck_776_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_tail_750_);
lean_inc(v_value_749_);
lean_inc(v_key_748_);
lean_dec(v_x_747_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_776_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; uint64_t v___y_756_; 
v___x_754_ = lean_array_get_size(v_x_746_);
if (lean_obj_tag(v_key_748_) == 0)
{
uint64_t v___x_774_; 
v___x_774_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_756_ = v___x_774_;
goto v___jp_755_;
}
else
{
uint64_t v_hash_775_; 
v_hash_775_ = lean_ctor_get_uint64(v_key_748_, sizeof(void*)*2);
v___y_756_ = v_hash_775_;
goto v___jp_755_;
}
v___jp_755_:
{
uint64_t v___x_757_; uint64_t v___x_758_; uint64_t v_fold_759_; uint64_t v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_757_ = 32ULL;
v___x_758_ = lean_uint64_shift_right(v___y_756_, v___x_757_);
v_fold_759_ = lean_uint64_xor(v___y_756_, v___x_758_);
v___x_760_ = 16ULL;
v___x_761_ = lean_uint64_shift_right(v_fold_759_, v___x_760_);
v___x_762_ = lean_uint64_xor(v_fold_759_, v___x_761_);
v___x_763_ = lean_uint64_to_usize(v___x_762_);
v___x_764_ = lean_usize_of_nat(v___x_754_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_sub(v___x_764_, v___x_765_);
v___x_767_ = lean_usize_land(v___x_763_, v___x_766_);
v___x_768_ = lean_array_uget_borrowed(v_x_746_, v___x_767_);
lean_inc(v___x_768_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 2, v___x_768_);
v___x_770_ = v___x_752_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_key_748_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_value_749_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v___x_768_);
v___x_770_ = v_reuseFailAlloc_773_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; 
v___x_771_ = lean_array_uset(v_x_746_, v___x_767_, v___x_770_);
v_x_746_ = v___x_771_;
v_x_747_ = v_tail_750_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_777_, lean_object* v_source_778_, lean_object* v_target_779_){
_start:
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = lean_array_get_size(v_source_778_);
v___x_781_ = lean_nat_dec_lt(v_i_777_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec_ref(v_source_778_);
lean_dec(v_i_777_);
return v_target_779_;
}
else
{
lean_object* v_es_782_; lean_object* v___x_783_; lean_object* v_source_784_; lean_object* v_target_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_es_782_ = lean_array_fget(v_source_778_, v_i_777_);
v___x_783_ = lean_box(0);
v_source_784_ = lean_array_fset(v_source_778_, v_i_777_, v___x_783_);
v_target_785_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_779_, v_es_782_);
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_add(v_i_777_, v___x_786_);
lean_dec(v_i_777_);
v_i_777_ = v___x_787_;
v_source_778_ = v_source_784_;
v_target_779_ = v_target_785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(lean_object* v_data_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_nbuckets_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_790_ = lean_array_get_size(v_data_789_);
v___x_791_ = lean_unsigned_to_nat(2u);
v_nbuckets_792_ = lean_nat_mul(v___x_790_, v___x_791_);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_box(0);
v___x_795_ = lean_mk_array(v_nbuckets_792_, v___x_794_);
v___x_796_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v___x_793_, v_data_789_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(lean_object* v_m_797_, lean_object* v_a_798_, lean_object* v_b_799_){
_start:
{
lean_object* v_size_800_; lean_object* v_buckets_801_; lean_object* v___x_802_; uint64_t v___y_804_; 
v_size_800_ = lean_ctor_get(v_m_797_, 0);
v_buckets_801_ = lean_ctor_get(v_m_797_, 1);
v___x_802_ = lean_array_get_size(v_buckets_801_);
if (lean_obj_tag(v_a_798_) == 0)
{
uint64_t v___x_841_; 
v___x_841_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_804_ = v___x_841_;
goto v___jp_803_;
}
else
{
uint64_t v_hash_842_; 
v_hash_842_ = lean_ctor_get_uint64(v_a_798_, sizeof(void*)*2);
v___y_804_ = v_hash_842_;
goto v___jp_803_;
}
v___jp_803_:
{
uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v_fold_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v___x_810_; size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v_bkt_816_; uint8_t v___x_817_; 
v___x_805_ = 32ULL;
v___x_806_ = lean_uint64_shift_right(v___y_804_, v___x_805_);
v_fold_807_ = lean_uint64_xor(v___y_804_, v___x_806_);
v___x_808_ = 16ULL;
v___x_809_ = lean_uint64_shift_right(v_fold_807_, v___x_808_);
v___x_810_ = lean_uint64_xor(v_fold_807_, v___x_809_);
v___x_811_ = lean_uint64_to_usize(v___x_810_);
v___x_812_ = lean_usize_of_nat(v___x_802_);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_sub(v___x_812_, v___x_813_);
v___x_815_ = lean_usize_land(v___x_811_, v___x_814_);
v_bkt_816_ = lean_array_uget_borrowed(v_buckets_801_, v___x_815_);
v___x_817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_798_, v_bkt_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_838_; 
lean_inc_ref(v_buckets_801_);
lean_inc(v_size_800_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_m_797_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_839_ = lean_ctor_get(v_m_797_, 1);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_m_797_, 0);
lean_dec(v_unused_840_);
v___x_819_ = v_m_797_;
v_isShared_820_ = v_isSharedCheck_838_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_m_797_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_838_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v_size_x27_822_; lean_object* v___x_823_; lean_object* v_buckets_x27_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v_size_x27_822_ = lean_nat_add(v_size_800_, v___x_821_);
lean_dec(v_size_800_);
lean_inc(v_bkt_816_);
v___x_823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_823_, 0, v_a_798_);
lean_ctor_set(v___x_823_, 1, v_b_799_);
lean_ctor_set(v___x_823_, 2, v_bkt_816_);
v_buckets_x27_824_ = lean_array_uset(v_buckets_801_, v___x_815_, v___x_823_);
v___x_825_ = lean_unsigned_to_nat(4u);
v___x_826_ = lean_nat_mul(v_size_x27_822_, v___x_825_);
v___x_827_ = lean_unsigned_to_nat(3u);
v___x_828_ = lean_nat_div(v___x_826_, v___x_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_array_get_size(v_buckets_x27_824_);
v___x_830_ = lean_nat_dec_le(v___x_828_, v___x_829_);
lean_dec(v___x_828_);
if (v___x_830_ == 0)
{
lean_object* v_val_831_; lean_object* v___x_833_; 
v_val_831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_buckets_x27_824_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_val_831_);
lean_ctor_set(v___x_819_, 0, v_size_x27_822_);
v___x_833_ = v___x_819_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_size_x27_822_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_val_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_836_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_buckets_x27_824_);
lean_ctor_set(v___x_819_, 0, v_size_x27_822_);
v___x_836_ = v___x_819_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_x27_822_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_buckets_x27_824_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_dec(v_b_799_);
lean_dec(v_a_798_);
return v_m_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_insert(lean_object* v_s_843_, lean_object* v_n_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_box(0);
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_s_843_, v_n_844_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0(lean_object* v_00_u03b2_847_, lean_object* v_m_848_, lean_object* v_a_849_, lean_object* v_b_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0___redArg(v_m_848_, v_a_849_, v_b_850_);
return v___x_851_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_856_, lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0(v_00_u03b2_856_, v_a_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec(v_a_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1(lean_object* v_00_u03b2_861_, lean_object* v_data_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1___redArg(v_data_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_864_, lean_object* v_i_865_, lean_object* v_source_866_, lean_object* v_target_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2___redArg(v_i_865_, v_source_866_, v_target_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_870_, v_x_871_);
return v___x_872_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(lean_object* v_m_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_buckets_875_; lean_object* v___x_876_; uint64_t v___y_878_; 
v_buckets_875_ = lean_ctor_get(v_m_873_, 1);
v___x_876_ = lean_array_get_size(v_buckets_875_);
if (lean_obj_tag(v_a_874_) == 0)
{
uint64_t v___x_892_; 
v___x_892_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_878_ = v___x_892_;
goto v___jp_877_;
}
else
{
uint64_t v_hash_893_; 
v_hash_893_ = lean_ctor_get_uint64(v_a_874_, sizeof(void*)*2);
v___y_878_ = v_hash_893_;
goto v___jp_877_;
}
v___jp_877_:
{
uint64_t v___x_879_; uint64_t v___x_880_; uint64_t v_fold_881_; uint64_t v___x_882_; uint64_t v___x_883_; uint64_t v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_879_ = 32ULL;
v___x_880_ = lean_uint64_shift_right(v___y_878_, v___x_879_);
v_fold_881_ = lean_uint64_xor(v___y_878_, v___x_880_);
v___x_882_ = 16ULL;
v___x_883_ = lean_uint64_shift_right(v_fold_881_, v___x_882_);
v___x_884_ = lean_uint64_xor(v_fold_881_, v___x_883_);
v___x_885_ = lean_uint64_to_usize(v___x_884_);
v___x_886_ = lean_usize_of_nat(v___x_876_);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_sub(v___x_886_, v___x_887_);
v___x_889_ = lean_usize_land(v___x_885_, v___x_888_);
v___x_890_ = lean_array_uget_borrowed(v_buckets_875_, v___x_889_);
v___x_891_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_NameHashSet_insert_spec__0_spec__0___redArg(v_a_874_, v___x_890_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg___boxed(lean_object* v_m_894_, lean_object* v_a_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_m_894_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameHashSet_contains(lean_object* v_s_898_, lean_object* v_n_899_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_s_898_, v_n_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_contains___boxed(lean_object* v_s_901_, lean_object* v_n_902_){
_start:
{
uint8_t v_res_903_; lean_object* v_r_904_; 
v_res_903_ = l_Lean_NameHashSet_contains(v_s_901_, v_n_902_);
lean_dec(v_n_902_);
lean_dec_ref(v_s_901_);
v_r_904_ = lean_box(v_res_903_);
return v_r_904_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(lean_object* v_00_u03b2_905_, lean_object* v_m_906_, lean_object* v_a_907_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___redArg(v_m_906_, v_a_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0___boxed(lean_object* v_00_u03b2_909_, lean_object* v_m_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_NameHashSet_contains_spec__0(v_00_u03b2_909_, v_m_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_m_910_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(lean_object* v_f_914_, lean_object* v_acc_915_, lean_object* v_a_916_){
_start:
{
if (lean_obj_tag(v_a_916_) == 0)
{
lean_dec_ref(v_f_914_);
return v_acc_915_;
}
else
{
lean_object* v_key_917_; lean_object* v_value_918_; lean_object* v_tail_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_930_; 
v_key_917_ = lean_ctor_get(v_a_916_, 0);
v_value_918_ = lean_ctor_get(v_a_916_, 1);
v_tail_919_ = lean_ctor_get(v_a_916_, 2);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_930_ == 0)
{
v___x_921_ = v_a_916_;
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_tail_919_);
lean_inc(v_value_918_);
lean_inc(v_key_917_);
lean_dec(v_a_916_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_930_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
lean_inc_ref(v_f_914_);
lean_inc(v_key_917_);
v___x_923_ = lean_apply_1(v_f_914_, v_key_917_);
v___x_924_ = lean_unbox(v___x_923_);
if (v___x_924_ == 0)
{
lean_del_object(v___x_921_);
lean_dec(v_value_918_);
lean_dec(v_key_917_);
v_a_916_ = v_tail_919_;
goto _start;
}
else
{
lean_object* v___x_927_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 2, v_acc_915_);
v___x_927_ = v___x_921_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_key_917_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_value_918_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_acc_915_);
v___x_927_ = v_reuseFailAlloc_929_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
v_acc_915_ = v___x_927_;
v_a_916_ = v_tail_919_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(lean_object* v_f_931_, size_t v_sz_932_, size_t v_i_933_, lean_object* v_bs_934_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_lt(v_i_933_, v_sz_932_);
if (v___x_935_ == 0)
{
lean_dec_ref(v_f_931_);
return v_bs_934_;
}
else
{
lean_object* v_v_936_; lean_object* v___x_937_; lean_object* v_bs_x27_938_; lean_object* v___x_939_; lean_object* v___x_940_; size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; 
v_v_936_ = lean_array_uget(v_bs_934_, v_i_933_);
v___x_937_ = lean_unsigned_to_nat(0u);
v_bs_x27_938_ = lean_array_uset(v_bs_934_, v_i_933_, v___x_937_);
v___x_939_ = lean_box(0);
lean_inc_ref(v_f_931_);
v___x_940_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__0(v_f_931_, v___x_939_, v_v_936_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_add(v_i_933_, v___x_941_);
v___x_943_ = lean_array_uset(v_bs_x27_938_, v_i_933_, v___x_940_);
v_i_933_ = v___x_942_;
v_bs_934_ = v___x_943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1___boxed(lean_object* v_f_945_, lean_object* v_sz_946_, lean_object* v_i_947_, lean_object* v_bs_948_){
_start:
{
size_t v_sz_boxed_949_; size_t v_i_boxed_950_; lean_object* v_res_951_; 
v_sz_boxed_949_ = lean_unbox_usize(v_sz_946_);
lean_dec(v_sz_946_);
v_i_boxed_950_ = lean_unbox_usize(v_i_947_);
lean_dec(v_i_947_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_945_, v_sz_boxed_949_, v_i_boxed_950_, v_bs_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(lean_object* v_as_952_, size_t v_i_953_, size_t v_stop_954_, lean_object* v_b_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = lean_usize_dec_eq(v_i_953_, v_stop_954_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; size_t v___x_960_; size_t v___x_961_; 
v___x_957_ = lean_array_uget_borrowed(v_as_952_, v_i_953_);
v___x_958_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_957_);
v___x_959_ = lean_nat_add(v_b_955_, v___x_958_);
lean_dec(v___x_958_);
lean_dec(v_b_955_);
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_953_, v___x_960_);
v_i_953_ = v___x_961_;
v_b_955_ = v___x_959_;
goto _start;
}
else
{
return v_b_955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2___boxed(lean_object* v_as_963_, lean_object* v_i_964_, lean_object* v_stop_965_, lean_object* v_b_966_){
_start:
{
size_t v_i_boxed_967_; size_t v_stop_boxed_968_; lean_object* v_res_969_; 
v_i_boxed_967_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_stop_boxed_968_ = lean_unbox_usize(v_stop_965_);
lean_dec(v_stop_965_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_as_963_, v_i_boxed_967_, v_stop_boxed_968_, v_b_966_);
lean_dec_ref(v_as_963_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(lean_object* v_f_970_, lean_object* v_m_971_){
_start:
{
lean_object* v_buckets_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_999_; 
v_buckets_972_ = lean_ctor_get(v_m_971_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_m_971_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; 
v_unused_1000_ = lean_ctor_get(v_m_971_, 0);
lean_dec(v_unused_1000_);
v___x_974_ = v_m_971_;
v_isShared_975_ = v_isSharedCheck_999_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_buckets_972_);
lean_dec(v_m_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_999_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
size_t v_sz_976_; size_t v___x_977_; lean_object* v_newBuckets_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v_sz_976_ = lean_array_size(v_buckets_972_);
v___x_977_ = ((size_t)0ULL);
v_newBuckets_978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__1(v_f_970_, v_sz_976_, v___x_977_, v_buckets_972_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_array_get_size(v_newBuckets_978_);
v___x_981_ = lean_nat_dec_lt(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_983_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_newBuckets_978_);
lean_ctor_set(v___x_974_, 0, v___x_979_);
v___x_983_ = v___x_974_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_newBuckets_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_le(v___x_980_, v___x_980_);
if (v___x_985_ == 0)
{
if (v___x_981_ == 0)
{
lean_object* v___x_987_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_newBuckets_978_);
lean_ctor_set(v___x_974_, 0, v___x_979_);
v___x_987_ = v___x_974_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_newBuckets_978_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
size_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_989_ = lean_usize_of_nat(v___x_980_);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_978_, v___x_977_, v___x_989_, v___x_979_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_newBuckets_978_);
lean_ctor_set(v___x_974_, 0, v___x_990_);
v___x_992_ = v___x_974_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_newBuckets_978_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
size_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_994_ = lean_usize_of_nat(v___x_980_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0_spec__2(v_newBuckets_978_, v___x_977_, v___x_994_, v___x_979_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_newBuckets_978_);
lean_ctor_set(v___x_974_, 0, v___x_995_);
v___x_997_ = v___x_974_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_newBuckets_978_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameHashSet_filter(lean_object* v_f_1001_, lean_object* v_s_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_NameHashSet_filter_spec__0(v_f_1001_, v_s_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1004_) == 0)
{
if (lean_obj_tag(v_x_1005_) == 0)
{
uint8_t v___x_1006_; 
v___x_1006_ = 1;
return v___x_1006_;
}
else
{
uint8_t v___x_1007_; 
v___x_1007_ = 0;
return v___x_1007_;
}
}
else
{
if (lean_obj_tag(v_x_1005_) == 0)
{
uint8_t v___x_1008_; 
v___x_1008_ = 0;
return v___x_1008_;
}
else
{
lean_object* v_head_1009_; lean_object* v_tail_1010_; lean_object* v_head_1011_; lean_object* v_tail_1012_; uint8_t v___x_1013_; 
v_head_1009_ = lean_ctor_get(v_x_1004_, 0);
v_tail_1010_ = lean_ctor_get(v_x_1004_, 1);
v_head_1011_ = lean_ctor_get(v_x_1005_, 0);
v_tail_1012_ = lean_ctor_get(v_x_1005_, 1);
v___x_1013_ = lean_nat_dec_eq(v_head_1009_, v_head_1011_);
if (v___x_1013_ == 0)
{
return v___x_1013_;
}
else
{
v_x_1004_ = v_tail_1010_;
v_x_1005_ = v_tail_1012_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0___boxed(lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_x_1015_, v_x_1016_);
lean_dec(v_x_1016_);
lean_dec(v_x_1015_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isPrefixOf(lean_object* v_v_u2081_1019_, lean_object* v_v_u2082_1020_){
_start:
{
lean_object* v_name_1021_; lean_object* v_imported_1022_; lean_object* v_ctx_1023_; lean_object* v_scopes_1024_; lean_object* v_name_1025_; lean_object* v_imported_1026_; lean_object* v_ctx_1027_; lean_object* v_scopes_1028_; uint8_t v___y_1030_; uint8_t v___x_1033_; 
v_name_1021_ = lean_ctor_get(v_v_u2081_1019_, 0);
v_imported_1022_ = lean_ctor_get(v_v_u2081_1019_, 1);
v_ctx_1023_ = lean_ctor_get(v_v_u2081_1019_, 2);
v_scopes_1024_ = lean_ctor_get(v_v_u2081_1019_, 3);
v_name_1025_ = lean_ctor_get(v_v_u2082_1020_, 0);
v_imported_1026_ = lean_ctor_get(v_v_u2082_1020_, 1);
v_ctx_1027_ = lean_ctor_get(v_v_u2082_1020_, 2);
v_scopes_1028_ = lean_ctor_get(v_v_u2082_1020_, 3);
v___x_1033_ = l_Lean_Name_isPrefixOf(v_name_1021_, v_name_1025_);
if (v___x_1033_ == 0)
{
v___y_1030_ = v___x_1033_;
goto v___jp_1029_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1024_, v_scopes_1028_);
v___y_1030_ = v___x_1034_;
goto v___jp_1029_;
}
v___jp_1029_:
{
if (v___y_1030_ == 0)
{
return v___y_1030_;
}
else
{
uint8_t v___x_1031_; 
v___x_1031_ = lean_name_eq(v_ctx_1023_, v_ctx_1027_);
if (v___x_1031_ == 0)
{
return v___x_1031_;
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_name_eq(v_imported_1022_, v_imported_1026_);
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isPrefixOf___boxed(lean_object* v_v_u2081_1035_, lean_object* v_v_u2082_1036_){
_start:
{
uint8_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Lean_MacroScopesView_isPrefixOf(v_v_u2081_1035_, v_v_u2082_1036_);
lean_dec_ref(v_v_u2082_1036_);
lean_dec_ref(v_v_u2081_1035_);
v_r_1038_ = lean_box(v_res_1037_);
return v_r_1038_;
}
}
LEAN_EXPORT uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object* v_v_u2081_1039_, lean_object* v_v_u2082_1040_){
_start:
{
lean_object* v_name_1041_; lean_object* v_imported_1042_; lean_object* v_ctx_1043_; lean_object* v_scopes_1044_; lean_object* v_name_1045_; lean_object* v_imported_1046_; lean_object* v_ctx_1047_; lean_object* v_scopes_1048_; uint8_t v___y_1050_; uint8_t v___x_1053_; 
v_name_1041_ = lean_ctor_get(v_v_u2081_1039_, 0);
v_imported_1042_ = lean_ctor_get(v_v_u2081_1039_, 1);
v_ctx_1043_ = lean_ctor_get(v_v_u2081_1039_, 2);
v_scopes_1044_ = lean_ctor_get(v_v_u2081_1039_, 3);
v_name_1045_ = lean_ctor_get(v_v_u2082_1040_, 0);
v_imported_1046_ = lean_ctor_get(v_v_u2082_1040_, 1);
v_ctx_1047_ = lean_ctor_get(v_v_u2082_1040_, 2);
v_scopes_1048_ = lean_ctor_get(v_v_u2082_1040_, 3);
v___x_1053_ = l_Lean_Name_isSuffixOf(v_name_1041_, v_name_1045_);
if (v___x_1053_ == 0)
{
v___y_1050_ = v___x_1053_;
goto v___jp_1049_;
}
else
{
uint8_t v___x_1054_; 
v___x_1054_ = l_List_beq___at___00Lean_MacroScopesView_isPrefixOf_spec__0(v_scopes_1044_, v_scopes_1048_);
v___y_1050_ = v___x_1054_;
goto v___jp_1049_;
}
v___jp_1049_:
{
if (v___y_1050_ == 0)
{
return v___y_1050_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_name_eq(v_ctx_1043_, v_ctx_1047_);
if (v___x_1051_ == 0)
{
return v___x_1051_;
}
else
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_name_eq(v_imported_1042_, v_imported_1046_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MacroScopesView_isSuffixOf___boxed(lean_object* v_v_u2081_1055_, lean_object* v_v_u2082_1056_){
_start:
{
uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_res_1057_ = l_Lean_MacroScopesView_isSuffixOf(v_v_u2081_1055_, v_v_u2082_1056_);
lean_dec_ref(v_v_u2082_1056_);
lean_dec_ref(v_v_u2081_1055_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_SSet(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
