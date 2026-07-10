// Lean compiler output
// Module: Lean.Meta.Tactic.Ext
// Imports: public import Init.Data.Array.InsertionSort public import Lean.Meta.DiscrTree
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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1 = (const lean_object*)&l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem_default = (const lean_object*)&l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem = (const lean_object*)&l_Lean_Meta_Ext_instInhabitedExtTheorem_default___closed__1_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "priority"};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "keys"};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12;
static const lean_string_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14;
static lean_once_cell_t l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Ext_instReprExtTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Ext_instReprExtTheorem_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_instReprExtTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Ext_instReprExtTheorem = (const lean_object*)&l_Lean_Meta_Ext_instReprExtTheorem___closed__0_value;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_instBEqExtTheorem_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instBEqExtTheorem_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Ext_instBEqExtTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Ext_instBEqExtTheorem_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_instBEqExtTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_instBEqExtTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Ext_instBEqExtTheorem = (const lean_object*)&l_Lean_Meta_Ext_instBEqExtTheorem___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Ext_instHashableExtTheorem_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instHashableExtTheorem_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Ext_instHashableExtTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Ext_instHashableExtTheorem_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_instHashableExtTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_instHashableExtTheorem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Ext_instHashableExtTheorem = (const lean_object*)&l_Lean_Meta_Ext_instHashableExtTheorem___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ext"};
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extExtension"};
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__3_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__4_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__5_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 38, 49, 9, 254, 103, 53, 15)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__6_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 231, 153, 85, 100, 182, 63, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_extExtension;
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_getExtTheorems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__0_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__1 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__1_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__2 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__2_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__3 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__3_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__4 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__4_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__5 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__5_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__6 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__6_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__7 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Ext_getExtTheorems___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__1_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__2_value)}};
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__8 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Ext_getExtTheorems___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__8_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__3_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__4_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__5_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__6_value)}};
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__9 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Ext_getExtTheorems___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__9_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__7_value)}};
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__10 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__10_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__11 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__11_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__12 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Cannot erase `[ext]` attribute from `"};
static const lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`: It does not have this attribute"};
static const lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__1(lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_nat_to_int(v_a_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(lean_object* v___y_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v___y_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_dec(v_x_14_);
return v_x_15_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_29_; 
v_head_17_ = lean_ctor_get(v_x_16_, 0);
v_tail_18_ = lean_ctor_get(v_x_16_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_29_ == 0)
{
v___x_20_ = v_x_16_;
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_head_17_);
lean_dec(v_x_16_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
lean_inc(v_x_14_);
if (v_isShared_21_ == 0)
{
lean_ctor_set_tag(v___x_20_, 5);
lean_ctor_set(v___x_20_, 1, v_x_14_);
lean_ctor_set(v___x_20_, 0, v_x_15_);
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_x_15_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_x_14_);
v___x_23_ = v_reuseFailAlloc_28_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_unsigned_to_nat(0u);
v___x_25_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v_head_17_, v___x_24_);
v___x_26_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_23_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v_x_15_ = v___x_26_;
v_x_16_ = v_tail_18_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2(lean_object* v_x_30_, lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_dec(v_x_30_);
return v_x_31_;
}
else
{
lean_object* v_head_33_; lean_object* v_tail_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_45_; 
v_head_33_ = lean_ctor_get(v_x_32_, 0);
v_tail_34_ = lean_ctor_get(v_x_32_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_45_ == 0)
{
v___x_36_ = v_x_32_;
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_tail_34_);
lean_inc(v_head_33_);
lean_dec(v_x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_45_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
lean_inc(v_x_30_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 5);
lean_ctor_set(v___x_36_, 1, v_x_30_);
lean_ctor_set(v___x_36_, 0, v_x_31_);
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_x_31_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_x_30_);
v___x_39_ = v_reuseFailAlloc_44_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = l_Lean_Meta_DiscrTree_instReprKey_repr(v_head_33_, v___x_40_);
v___x_42_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_39_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2_spec__3(v_x_30_, v___x_42_, v_tail_34_);
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0(lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_48_; 
lean_dec(v_x_47_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
else
{
lean_object* v_tail_49_; 
v_tail_49_ = lean_ctor_get(v_x_46_, 1);
if (lean_obj_tag(v_tail_49_) == 0)
{
lean_object* v_head_50_; lean_object* v___x_51_; 
lean_dec(v_x_47_);
v_head_50_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_50_);
lean_dec_ref_known(v_x_46_, 2);
v___x_51_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(v_head_50_);
return v___x_51_;
}
else
{
lean_object* v_head_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_tail_49_);
v_head_52_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_52_);
lean_dec_ref_known(v_x_46_, 2);
v___x_53_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(v_head_52_);
v___x_54_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0_spec__2(v_x_47_, v___x_53_, v_tail_49_);
return v___x_54_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__0));
v___x_64_ = lean_string_length(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__5);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0(lean_object* v_xs_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_array_get_size(v_xs_74_);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_78_ = lean_array_to_list(v_xs_74_);
v___x_79_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__3));
v___x_80_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0(v___x_78_, v___x_79_);
v___x_81_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__6);
v___x_82_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__7));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_80_);
v___x_84_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__8));
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = l_Std_Format_fill(v___x_86_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; 
lean_dec_ref(v_xs_74_);
v___x_88_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__10));
return v___x_88_;
}
}
}
static lean_object* _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(12u);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(8u);
v___x_111_ = lean_nat_to_int(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__0));
v___x_114_ = lean_string_length(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_obj_once(&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14, &l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14_once, _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__14);
v___x_116_ = lean_nat_to_int(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg(lean_object* v_x_121_){
_start:
{
lean_object* v_declName_122_; lean_object* v_priority_123_; lean_object* v_keys_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_declName_122_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_declName_122_);
v_priority_123_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_priority_123_);
v_keys_124_ = lean_ctor_get(v_x_121_, 2);
lean_inc_ref(v_keys_124_);
lean_dec_ref(v_x_121_);
v___x_125_ = ((lean_object*)(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__5));
v___x_126_ = ((lean_object*)(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__6));
v___x_127_ = lean_obj_once(&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7, &l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7_once, _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__7);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = l_Lean_Name_reprPrec(v_declName_122_, v___x_128_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_127_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = 0;
v___x_132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_131_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_126_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0___closed__2));
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_box(1);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = ((lean_object*)(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__9));
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_125_);
v___x_141_ = l_Nat_reprFast(v_priority_123_);
v___x_142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
v___x_143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_127_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*1, v___x_131_);
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_140_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_134_);
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_136_);
v___x_148_ = ((lean_object*)(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__11));
v___x_149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v___x_125_);
v___x_151_ = lean_obj_once(&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12, &l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12_once, _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__12);
v___x_152_ = l_Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0(v_keys_124_);
v___x_153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_131_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_150_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_obj_once(&l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15, &l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15_once, _init_l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__15);
v___x_157_ = ((lean_object*)(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__16));
v___x_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_155_);
v___x_159_ = ((lean_object*)(l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg___closed__17));
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_156_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_131_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr(lean_object* v_x_163_, lean_object* v_prec_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_Ext_instReprExtTheorem_repr___redArg(v_x_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instReprExtTheorem_repr___boxed(lean_object* v_x_166_, lean_object* v_prec_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_Ext_instReprExtTheorem_repr(v_x_166_, v_prec_167_);
lean_dec(v_prec_167_);
return v_res_168_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(lean_object* v_xs_171_, lean_object* v_ys_172_, lean_object* v_x_173_){
_start:
{
lean_object* v_zero_174_; uint8_t v_isZero_175_; 
v_zero_174_ = lean_unsigned_to_nat(0u);
v_isZero_175_ = lean_nat_dec_eq(v_x_173_, v_zero_174_);
if (v_isZero_175_ == 1)
{
lean_dec(v_x_173_);
return v_isZero_175_;
}
else
{
lean_object* v_one_176_; lean_object* v_n_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_one_176_ = lean_unsigned_to_nat(1u);
v_n_177_ = lean_nat_sub(v_x_173_, v_one_176_);
lean_dec(v_x_173_);
v___x_178_ = lean_array_fget_borrowed(v_xs_171_, v_n_177_);
v___x_179_ = lean_array_fget_borrowed(v_ys_172_, v_n_177_);
v___x_180_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v_n_177_);
return v___x_180_;
}
else
{
v_x_173_ = v_n_177_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg___boxed(lean_object* v_xs_182_, lean_object* v_ys_183_, lean_object* v_x_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(v_xs_182_, v_ys_183_, v_x_184_);
lean_dec_ref(v_ys_183_);
lean_dec_ref(v_xs_182_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_instBEqExtTheorem_beq(lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
lean_object* v_declName_189_; lean_object* v_priority_190_; lean_object* v_keys_191_; lean_object* v_declName_192_; lean_object* v_priority_193_; lean_object* v_keys_194_; uint8_t v___x_195_; 
v_declName_189_ = lean_ctor_get(v_x_187_, 0);
v_priority_190_ = lean_ctor_get(v_x_187_, 1);
v_keys_191_ = lean_ctor_get(v_x_187_, 2);
v_declName_192_ = lean_ctor_get(v_x_188_, 0);
v_priority_193_ = lean_ctor_get(v_x_188_, 1);
v_keys_194_ = lean_ctor_get(v_x_188_, 2);
v___x_195_ = lean_name_eq(v_declName_189_, v_declName_192_);
if (v___x_195_ == 0)
{
return v___x_195_;
}
else
{
uint8_t v___x_196_; 
v___x_196_ = lean_nat_dec_eq(v_priority_190_, v_priority_193_);
if (v___x_196_ == 0)
{
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_197_ = lean_array_get_size(v_keys_191_);
v___x_198_ = lean_array_get_size(v_keys_194_);
v___x_199_ = lean_nat_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(v_keys_191_, v_keys_194_, v___x_197_);
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instBEqExtTheorem_beq___boxed(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Meta_Ext_instBEqExtTheorem_beq(v_x_201_, v_x_202_);
lean_dec_ref(v_x_202_);
lean_dec_ref(v_x_201_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0(lean_object* v_xs_205_, lean_object* v_ys_206_, lean_object* v_hsz_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___redArg(v_xs_205_, v_ys_206_, v_x_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0___boxed(lean_object* v_xs_211_, lean_object* v_ys_212_, lean_object* v_hsz_213_, lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Array_isEqvAux___at___00Lean_Meta_Ext_instBEqExtTheorem_beq_spec__0(v_xs_211_, v_ys_212_, v_hsz_213_, v_x_214_, v_x_215_);
lean_dec_ref(v_ys_212_);
lean_dec_ref(v_xs_211_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(lean_object* v_as_220_, size_t v_i_221_, size_t v_stop_222_, uint64_t v_b_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = lean_usize_dec_eq(v_i_221_, v_stop_222_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; size_t v___x_228_; size_t v___x_229_; 
v___x_225_ = lean_array_uget_borrowed(v_as_220_, v_i_221_);
v___x_226_ = l_Lean_Meta_DiscrTree_Key_hash(v___x_225_);
v___x_227_ = lean_uint64_mix_hash(v_b_223_, v___x_226_);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_221_, v___x_228_);
v_i_221_ = v___x_229_;
v_b_223_ = v___x_227_;
goto _start;
}
else
{
return v_b_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0___boxed(lean_object* v_as_231_, lean_object* v_i_232_, lean_object* v_stop_233_, lean_object* v_b_234_){
_start:
{
size_t v_i_boxed_235_; size_t v_stop_boxed_236_; uint64_t v_b_boxed_237_; uint64_t v_res_238_; lean_object* v_r_239_; 
v_i_boxed_235_ = lean_unbox_usize(v_i_232_);
lean_dec(v_i_232_);
v_stop_boxed_236_ = lean_unbox_usize(v_stop_233_);
lean_dec(v_stop_233_);
v_b_boxed_237_ = lean_unbox_uint64(v_b_234_);
lean_dec_ref(v_b_234_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_as_231_, v_i_boxed_235_, v_stop_boxed_236_, v_b_boxed_237_);
lean_dec_ref(v_as_231_);
v_r_239_ = lean_box_uint64(v_res_238_);
return v_r_239_;
}
}
static uint64_t _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0(void){
_start:
{
lean_object* v___x_240_; uint64_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1723u);
v___x_241_ = lean_uint64_of_nat(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Ext_instHashableExtTheorem_hash(lean_object* v_x_242_){
_start:
{
lean_object* v_declName_243_; lean_object* v_priority_244_; lean_object* v_keys_245_; uint64_t v___x_246_; uint64_t v___y_248_; 
v_declName_243_ = lean_ctor_get(v_x_242_, 0);
v_priority_244_ = lean_ctor_get(v_x_242_, 1);
v_keys_245_ = lean_ctor_get(v_x_242_, 2);
v___x_246_ = 0ULL;
if (lean_obj_tag(v_declName_243_) == 0)
{
uint64_t v___x_267_; 
v___x_267_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_248_ = v___x_267_;
goto v___jp_247_;
}
else
{
uint64_t v_hash_268_; 
v_hash_268_ = lean_ctor_get_uint64(v_declName_243_, sizeof(void*)*2);
v___y_248_ = v_hash_268_;
goto v___jp_247_;
}
v___jp_247_:
{
uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_249_ = lean_uint64_mix_hash(v___x_246_, v___y_248_);
v___x_250_ = lean_uint64_of_nat(v_priority_244_);
v___x_251_ = lean_uint64_mix_hash(v___x_249_, v___x_250_);
v___x_252_ = 7ULL;
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_array_get_size(v_keys_245_);
v___x_255_ = lean_nat_dec_lt(v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
uint64_t v___x_256_; 
v___x_256_ = lean_uint64_mix_hash(v___x_251_, v___x_252_);
return v___x_256_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = lean_nat_dec_le(v___x_254_, v___x_254_);
if (v___x_257_ == 0)
{
if (v___x_255_ == 0)
{
uint64_t v___x_258_; 
v___x_258_ = lean_uint64_mix_hash(v___x_251_, v___x_252_);
return v___x_258_;
}
else
{
size_t v___x_259_; size_t v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; 
v___x_259_ = ((size_t)0ULL);
v___x_260_ = lean_usize_of_nat(v___x_254_);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_keys_245_, v___x_259_, v___x_260_, v___x_252_);
v___x_262_ = lean_uint64_mix_hash(v___x_251_, v___x_261_);
return v___x_262_;
}
}
else
{
size_t v___x_263_; size_t v___x_264_; uint64_t v___x_265_; uint64_t v___x_266_; 
v___x_263_ = ((size_t)0ULL);
v___x_264_ = lean_usize_of_nat(v___x_254_);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_keys_245_, v___x_263_, v___x_264_, v___x_252_);
v___x_266_ = lean_uint64_mix_hash(v___x_251_, v___x_265_);
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instHashableExtTheorem_hash___boxed(lean_object* v_x_269_){
_start:
{
uint64_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Lean_Meta_Ext_instHashableExtTheorem_hash(v_x_269_);
lean_dec_ref(v_x_269_);
v_r_271_ = lean_box_uint64(v_res_270_);
return v_r_271_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_274_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(lean_object* v_00_u03b2_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(lean_box(0));
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2);
v___x_284_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v_a_289_);
lean_inc_ref_n(v___x_290_, 2);
v___x_291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_x_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v_x_292_, v_a_293_);
lean_dec_ref(v_x_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15(lean_object* v_xs_295_, lean_object* v_v_296_, lean_object* v_i_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_array_get_size(v_xs_295_);
v___x_299_ = lean_nat_dec_lt(v_i_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v_i_297_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_array_fget_borrowed(v_xs_295_, v_i_297_);
v___x_302_ = lean_name_eq(v___x_301_, v_v_296_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v___x_304_ = lean_nat_add(v_i_297_, v___x_303_);
lean_dec(v_i_297_);
v_i_297_ = v___x_304_;
goto _start;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v_i_297_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15___boxed(lean_object* v_xs_307_, lean_object* v_v_308_, lean_object* v_i_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15(v_xs_307_, v_v_308_, v_i_309_);
lean_dec(v_v_308_);
lean_dec_ref(v_xs_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object* v_xs_311_, lean_object* v_v_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15(v_xs_311_, v_v_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9___boxed(lean_object* v_xs_315_, lean_object* v_v_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_xs_315_, v_v_316_);
lean_dec(v_v_316_);
lean_dec_ref(v_xs_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_x_318_, size_t v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v_es_321_; lean_object* v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v_j_325_; lean_object* v_entry_326_; 
v_es_321_ = lean_ctor_get(v_x_318_, 0);
v___x_322_ = lean_box(2);
v___x_323_ = ((size_t)31ULL);
v___x_324_ = lean_usize_land(v_x_319_, v___x_323_);
v_j_325_ = lean_usize_to_nat(v___x_324_);
v_entry_326_ = lean_array_get(v___x_322_, v_es_321_, v_j_325_);
switch(lean_obj_tag(v_entry_326_))
{
case 0:
{
lean_object* v_key_327_; uint8_t v___x_328_; 
v_key_327_ = lean_ctor_get(v_entry_326_, 0);
lean_inc(v_key_327_);
lean_dec_ref_known(v_entry_326_, 2);
v___x_328_ = lean_name_eq(v_x_320_, v_key_327_);
lean_dec(v_key_327_);
if (v___x_328_ == 0)
{
lean_dec(v_j_325_);
return v_x_318_;
}
else
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
lean_inc_ref(v_es_321_);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v_x_318_, 0);
lean_dec(v_unused_337_);
v___x_330_ = v_x_318_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_dec(v_x_318_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_array_set(v_es_321_, v_j_325_, v___x_322_);
lean_dec(v_j_325_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
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
case 1:
{
lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_372_; 
lean_inc_ref(v_es_321_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v_x_318_, 0);
lean_dec(v_unused_373_);
v___x_339_ = v_x_318_;
v_isShared_340_ = v_isSharedCheck_372_;
goto v_resetjp_338_;
}
else
{
lean_dec(v_x_318_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_372_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_node_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_371_; 
v_node_341_ = lean_ctor_get(v_entry_326_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_entry_326_);
if (v_isSharedCheck_371_ == 0)
{
v___x_343_ = v_entry_326_;
v_isShared_344_ = v_isSharedCheck_371_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_node_341_);
lean_dec(v_entry_326_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_371_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
size_t v___x_345_; lean_object* v_entries_346_; size_t v___x_347_; lean_object* v_newNode_348_; lean_object* v___x_349_; 
v___x_345_ = ((size_t)5ULL);
v_entries_346_ = lean_array_set(v_es_321_, v_j_325_, v___x_322_);
v___x_347_ = lean_usize_shift_right(v_x_319_, v___x_345_);
v_newNode_348_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_node_341_, v___x_347_, v_x_320_);
lean_inc_ref(v_newNode_348_);
v___x_349_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v___x_351_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v_newNode_348_);
v___x_351_ = v___x_343_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_newNode_348_);
v___x_351_ = v_reuseFailAlloc_356_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_array_set(v_entries_346_, v_j_325_, v___x_351_);
lean_dec(v_j_325_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_352_);
v___x_354_ = v___x_339_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_val_357_; lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v_newNode_348_);
lean_del_object(v___x_343_);
v_val_357_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___x_349_, 1);
v_fst_358_ = lean_ctor_get(v_val_357_, 0);
v_snd_359_ = lean_ctor_get(v_val_357_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_val_357_);
if (v_isSharedCheck_370_ == 0)
{
v___x_361_ = v_val_357_;
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snd_359_);
lean_inc(v_fst_358_);
lean_dec(v_val_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_fst_358_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_snd_359_);
v___x_364_ = v_reuseFailAlloc_369_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = lean_array_set(v_entries_346_, v_j_325_, v___x_364_);
lean_dec(v_j_325_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_365_);
v___x_367_ = v___x_339_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
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
}
}
}
default: 
{
lean_dec(v_j_325_);
return v_x_318_;
}
}
}
else
{
lean_object* v_ks_374_; lean_object* v_vs_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_389_; 
v_ks_374_ = lean_ctor_get(v_x_318_, 0);
v_vs_375_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_389_ == 0)
{
v___x_377_ = v_x_318_;
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_vs_375_);
lean_inc(v_ks_374_);
lean_dec(v_x_318_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; 
v___x_379_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_ks_374_, v_x_320_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_381_; 
if (v_isShared_378_ == 0)
{
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_ks_374_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_vs_375_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v_val_383_; lean_object* v_keys_x27_384_; lean_object* v_vals_x27_385_; lean_object* v___x_387_; 
v_val_383_ = lean_ctor_get(v___x_379_, 0);
lean_inc_n(v_val_383_, 2);
lean_dec_ref_known(v___x_379_, 1);
v_keys_x27_384_ = l_Array_eraseIdx___redArg(v_ks_374_, v_val_383_);
v_vals_x27_385_ = l_Array_eraseIdx___redArg(v_vs_375_, v_val_383_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v_vals_x27_385_);
lean_ctor_set(v___x_377_, 0, v_keys_x27_384_);
v___x_387_ = v___x_377_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_keys_x27_384_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_vals_x27_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
size_t v_x_1799__boxed_393_; lean_object* v_res_394_; 
v_x_1799__boxed_393_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_res_394_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_390_, v_x_1799__boxed_393_, v_x_392_);
lean_dec(v_x_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
uint64_t v___y_398_; 
if (lean_obj_tag(v_x_396_) == 0)
{
uint64_t v___x_401_; 
v___x_401_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_398_ = v___x_401_;
goto v___jp_397_;
}
else
{
uint64_t v_hash_402_; 
v_hash_402_ = lean_ctor_get_uint64(v_x_396_, sizeof(void*)*2);
v___y_398_ = v_hash_402_;
goto v___jp_397_;
}
v___jp_397_:
{
size_t v_h_399_; lean_object* v___x_400_; 
v_h_399_ = lean_uint64_to_usize(v___y_398_);
v___x_400_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_395_, v_h_399_, v_x_396_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_403_, v_x_404_);
lean_dec(v_x_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_ks_410_; lean_object* v_vs_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_435_; 
v_ks_410_ = lean_ctor_get(v_x_406_, 0);
v_vs_411_ = lean_ctor_get(v_x_406_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_406_);
if (v_isSharedCheck_435_ == 0)
{
v___x_413_ = v_x_406_;
v_isShared_414_ = v_isSharedCheck_435_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_vs_411_);
lean_inc(v_ks_410_);
lean_dec(v_x_406_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_435_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_array_get_size(v_ks_410_);
v___x_416_ = lean_nat_dec_lt(v_x_407_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec(v_x_407_);
v___x_417_ = lean_array_push(v_ks_410_, v_x_408_);
v___x_418_ = lean_array_push(v_vs_411_, v_x_409_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_418_);
lean_ctor_set(v___x_413_, 0, v___x_417_);
v___x_420_ = v___x_413_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v_k_x27_422_; uint8_t v___x_423_; 
v_k_x27_422_ = lean_array_fget_borrowed(v_ks_410_, v_x_407_);
v___x_423_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_408_, v_k_x27_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_425_; 
if (v_isShared_414_ == 0)
{
v___x_425_ = v___x_413_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_ks_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_vs_411_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_x_407_, v___x_426_);
lean_dec(v_x_407_);
v_x_406_ = v___x_425_;
v_x_407_ = v___x_427_;
goto _start;
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = lean_array_fset(v_ks_410_, v_x_407_, v_x_408_);
v___x_431_ = lean_array_fset(v_vs_411_, v_x_407_, v_x_409_);
lean_dec(v_x_407_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_431_);
lean_ctor_set(v___x_413_, 0, v___x_430_);
v___x_433_ = v___x_413_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_n_436_, lean_object* v_k_437_, lean_object* v_v_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(v_n_436_, v___x_439_, v_k_437_, v_v_438_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(lean_object* v_x_442_, size_t v_x_443_, size_t v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_442_) == 0)
{
lean_object* v_es_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v_j_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_es_447_ = lean_ctor_get(v_x_442_, 0);
v___x_448_ = ((size_t)31ULL);
v___x_449_ = lean_usize_land(v_x_443_, v___x_448_);
v_j_450_ = lean_usize_to_nat(v___x_449_);
v___x_451_ = lean_array_get_size(v_es_447_);
v___x_452_ = lean_nat_dec_lt(v_j_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_dec(v_j_450_);
lean_dec(v_x_446_);
lean_dec(v_x_445_);
return v_x_442_;
}
else
{
lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_491_; 
lean_inc_ref(v_es_447_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_x_442_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v_x_442_, 0);
lean_dec(v_unused_492_);
v___x_454_ = v_x_442_;
v_isShared_455_ = v_isSharedCheck_491_;
goto v_resetjp_453_;
}
else
{
lean_dec(v_x_442_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_491_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_v_456_; lean_object* v___x_457_; lean_object* v_xs_x27_458_; lean_object* v___y_460_; 
v_v_456_ = lean_array_fget(v_es_447_, v_j_450_);
v___x_457_ = lean_box(0);
v_xs_x27_458_ = lean_array_fset(v_es_447_, v_j_450_, v___x_457_);
switch(lean_obj_tag(v_v_456_))
{
case 0:
{
lean_object* v_key_465_; lean_object* v_val_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_476_; 
v_key_465_ = lean_ctor_get(v_v_456_, 0);
v_val_466_ = lean_ctor_get(v_v_456_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_v_456_);
if (v_isSharedCheck_476_ == 0)
{
v___x_468_ = v_v_456_;
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_val_466_);
lean_inc(v_key_465_);
lean_dec(v_v_456_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
uint8_t v___x_470_; 
v___x_470_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_445_, v_key_465_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_del_object(v___x_468_);
v___x_471_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_465_, v_val_466_, v_x_445_, v_x_446_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
v___y_460_ = v___x_472_;
goto v___jp_459_;
}
else
{
lean_object* v___x_474_; 
lean_dec(v_val_466_);
lean_dec(v_key_465_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v_x_446_);
lean_ctor_set(v___x_468_, 0, v_x_445_);
v___x_474_ = v___x_468_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_x_445_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_x_446_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
v___y_460_ = v___x_474_;
goto v___jp_459_;
}
}
}
}
case 1:
{
lean_object* v_node_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_489_; 
v_node_477_ = lean_ctor_get(v_v_456_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_v_456_);
if (v_isSharedCheck_489_ == 0)
{
v___x_479_ = v_v_456_;
v_isShared_480_ = v_isSharedCheck_489_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_node_477_);
lean_dec(v_v_456_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_489_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_usize_shift_right(v_x_443_, v___x_481_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_x_444_, v___x_483_);
v___x_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_node_477_, v___x_482_, v___x_484_, v_x_445_, v_x_446_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_485_);
v___x_487_ = v___x_479_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v___y_460_ = v___x_487_;
goto v___jp_459_;
}
}
}
default: 
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_x_445_);
lean_ctor_set(v___x_490_, 1, v_x_446_);
v___y_460_ = v___x_490_;
goto v___jp_459_;
}
}
v___jp_459_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_array_fset(v_xs_x27_458_, v_j_450_, v___y_460_);
lean_dec(v_j_450_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_461_);
v___x_463_ = v___x_454_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
else
{
lean_object* v_ks_493_; lean_object* v_vs_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_514_; 
v_ks_493_ = lean_ctor_get(v_x_442_, 0);
v_vs_494_ = lean_ctor_get(v_x_442_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_442_);
if (v_isSharedCheck_514_ == 0)
{
v___x_496_ = v_x_442_;
v_isShared_497_ = v_isSharedCheck_514_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_vs_494_);
lean_inc(v_ks_493_);
lean_dec(v_x_442_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_514_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_ks_493_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_vs_494_);
v___x_499_ = v_reuseFailAlloc_513_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v_newNode_500_; uint8_t v___y_502_; size_t v___x_508_; uint8_t v___x_509_; 
v_newNode_500_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(v___x_499_, v_x_445_, v_x_446_);
v___x_508_ = ((size_t)7ULL);
v___x_509_ = lean_usize_dec_le(v___x_508_, v_x_444_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_500_);
v___x_511_ = lean_unsigned_to_nat(4u);
v___x_512_ = lean_nat_dec_lt(v___x_510_, v___x_511_);
lean_dec(v___x_510_);
v___y_502_ = v___x_512_;
goto v___jp_501_;
}
else
{
v___y_502_ = v___x_509_;
goto v___jp_501_;
}
v___jp_501_:
{
if (v___y_502_ == 0)
{
lean_object* v_ks_503_; lean_object* v_vs_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_ks_503_ = lean_ctor_get(v_newNode_500_, 0);
lean_inc_ref(v_ks_503_);
v_vs_504_ = lean_ctor_get(v_newNode_500_, 1);
lean_inc_ref(v_vs_504_);
lean_dec_ref(v_newNode_500_);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0);
v___x_507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(v_x_444_, v_ks_503_, v_vs_504_, v___x_505_, v___x_506_);
lean_dec_ref(v_vs_504_);
lean_dec_ref(v_ks_503_);
return v___x_507_;
}
else
{
return v_newNode_500_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(size_t v_depth_515_, lean_object* v_keys_516_, lean_object* v_vals_517_, lean_object* v_i_518_, lean_object* v_entries_519_){
_start:
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_array_get_size(v_keys_516_);
v___x_521_ = lean_nat_dec_lt(v_i_518_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec(v_i_518_);
return v_entries_519_;
}
else
{
lean_object* v_k_522_; lean_object* v_v_523_; uint64_t v___x_524_; size_t v_h_525_; size_t v___x_526_; lean_object* v___x_527_; size_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v_h_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_k_522_ = lean_array_fget_borrowed(v_keys_516_, v_i_518_);
v_v_523_ = lean_array_fget_borrowed(v_vals_517_, v_i_518_);
v___x_524_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_522_);
v_h_525_ = lean_uint64_to_usize(v___x_524_);
v___x_526_ = ((size_t)5ULL);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_sub(v_depth_515_, v___x_528_);
v___x_530_ = lean_usize_mul(v___x_526_, v___x_529_);
v_h_531_ = lean_usize_shift_right(v_h_525_, v___x_530_);
v___x_532_ = lean_nat_add(v_i_518_, v___x_527_);
lean_dec(v_i_518_);
lean_inc(v_v_523_);
lean_inc(v_k_522_);
v___x_533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_entries_519_, v_h_531_, v_depth_515_, v_k_522_, v_v_523_);
v_i_518_ = v___x_532_;
v_entries_519_ = v___x_533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_depth_535_, lean_object* v_keys_536_, lean_object* v_vals_537_, lean_object* v_i_538_, lean_object* v_entries_539_){
_start:
{
size_t v_depth_boxed_540_; lean_object* v_res_541_; 
v_depth_boxed_540_ = lean_unbox_usize(v_depth_535_);
lean_dec(v_depth_535_);
v_res_541_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(v_depth_boxed_540_, v_keys_536_, v_vals_537_, v_i_538_, v_entries_539_);
lean_dec_ref(v_vals_537_);
lean_dec_ref(v_keys_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
size_t v_x_2028__boxed_547_; size_t v_x_2029__boxed_548_; lean_object* v_res_549_; 
v_x_2028__boxed_547_ = lean_unbox_usize(v_x_543_);
lean_dec(v_x_543_);
v_x_2029__boxed_548_ = lean_unbox_usize(v_x_544_);
lean_dec(v_x_544_);
v_res_549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_x_542_, v_x_2028__boxed_547_, v_x_2029__boxed_548_, v_x_545_, v_x_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9(lean_object* v_xs_550_, lean_object* v_v_551_, lean_object* v_i_552_){
_start:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_array_get_size(v_xs_550_);
v___x_554_ = lean_nat_dec_lt(v_i_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec(v_i_552_);
v___x_555_ = lean_box(0);
return v___x_555_;
}
else
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_array_fget_borrowed(v_xs_550_, v_i_552_);
v___x_557_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_556_, v_v_551_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_add(v_i_552_, v___x_558_);
lean_dec(v_i_552_);
v_i_552_ = v___x_559_;
goto _start;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_i_552_);
return v___x_561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_xs_562_, lean_object* v_v_563_, lean_object* v_i_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9(v_xs_562_, v_v_563_, v_i_564_);
lean_dec(v_v_563_);
lean_dec_ref(v_xs_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(lean_object* v_xs_566_, lean_object* v_v_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9(v_xs_566_, v_v_567_, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4___boxed(lean_object* v_xs_570_, lean_object* v_v_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(v_xs_570_, v_v_571_);
lean_dec(v_v_571_);
lean_dec_ref(v_xs_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(lean_object* v_x_573_, lean_object* v_keys_574_, lean_object* v_v_575_, lean_object* v_k_576_, lean_object* v_x_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_c_580_; lean_object* v___x_581_; 
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_x_573_, v___x_578_);
v_c_580_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_574_, v_v_575_, v___x_579_);
lean_dec(v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_581_, 0, v_k_576_);
lean_ctor_set(v___x_581_, 1, v_c_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_582_, lean_object* v_keys_583_, lean_object* v_v_584_, lean_object* v_k_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_582_, v_keys_583_, v_v_584_, v_k_585_, v_x_586_);
lean_dec_ref(v_keys_583_);
lean_dec(v_x_582_);
return v_res_587_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
lean_object* v_fst_590_; lean_object* v_fst_591_; uint8_t v___x_592_; 
v_fst_590_ = lean_ctor_get(v_a_588_, 0);
v_fst_591_ = lean_ctor_get(v_b_589_, 0);
v___x_592_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_590_, v_fst_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_593_, lean_object* v_b_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_a_593_, v_b_594_);
lean_dec_ref(v_b_594_);
lean_dec_ref(v_a_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_vs_597_, lean_object* v_v_598_, lean_object* v_i_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_vs_597_);
v___x_601_ = lean_nat_dec_lt(v_i_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v_i_599_);
v___x_602_ = lean_array_push(v_vs_597_, v_v_598_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_array_fget_borrowed(v_vs_597_, v_i_599_);
v___x_604_ = l_Lean_Meta_Ext_instBEqExtTheorem_beq(v_v_598_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_add(v_i_599_, v___x_605_);
lean_dec(v_i_599_);
v_i_599_ = v___x_606_;
goto _start;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_array_fset(v_vs_597_, v_i_599_, v_v_598_);
lean_dec(v_i_599_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_vs_609_, lean_object* v_v_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_vs_609_, v_v_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_617_, lean_object* v_keys_618_, lean_object* v_v_619_, lean_object* v_k_620_, lean_object* v_as_621_, lean_object* v_k_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v_mid_627_; lean_object* v_midVal_628_; uint8_t v___x_629_; 
v___x_625_ = lean_nat_add(v_x_623_, v_x_624_);
v___x_626_ = lean_unsigned_to_nat(1u);
v_mid_627_ = lean_nat_shiftr(v___x_625_, v___x_626_);
lean_dec(v___x_625_);
v_midVal_628_ = lean_array_fget(v_as_621_, v_mid_627_);
v___x_629_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_midVal_628_, v_k_622_);
if (v___x_629_ == 0)
{
uint8_t v___x_630_; 
lean_dec(v_x_624_);
v___x_630_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_k_622_, v_midVal_628_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; uint8_t v___x_632_; 
lean_dec(v_x_623_);
v___x_631_ = lean_array_get_size(v_as_621_);
v___x_632_ = lean_nat_dec_lt(v_mid_627_, v___x_631_);
if (v___x_632_ == 0)
{
lean_dec(v_midVal_628_);
lean_dec(v_mid_627_);
lean_dec(v_k_620_);
lean_dec_ref(v_v_619_);
return v_as_621_;
}
else
{
lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_645_; 
v_snd_633_ = lean_ctor_get(v_midVal_628_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_midVal_628_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_midVal_628_, 0);
lean_dec(v_unused_646_);
v___x_635_ = v_midVal_628_;
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_dec(v_midVal_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v_xs_x27_638_; lean_object* v___x_639_; lean_object* v_c_640_; lean_object* v___x_642_; 
v___x_637_ = lean_box(0);
v_xs_x27_638_ = lean_array_fset(v_as_621_, v_mid_627_, v___x_637_);
v___x_639_ = lean_nat_add(v_x_617_, v___x_626_);
v_c_640_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_618_, v_v_619_, v___x_639_, v_snd_633_);
lean_dec(v___x_639_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v_c_640_);
lean_ctor_set(v___x_635_, 0, v_k_620_);
v___x_642_ = v___x_635_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_k_620_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_c_640_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_array_fset(v_xs_x27_638_, v_mid_627_, v___x_642_);
lean_dec(v_mid_627_);
return v___x_643_;
}
}
}
}
else
{
lean_dec(v_midVal_628_);
v_x_624_ = v_mid_627_;
goto _start;
}
}
else
{
uint8_t v___x_648_; 
lean_dec(v_midVal_628_);
v___x_648_ = lean_nat_dec_eq(v_mid_627_, v_x_623_);
if (v___x_648_ == 0)
{
lean_dec(v_x_623_);
v_x_623_ = v_mid_627_;
goto _start;
}
else
{
lean_object* v___x_650_; lean_object* v_c_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v_j_654_; lean_object* v_as_655_; lean_object* v___x_656_; 
lean_dec(v_mid_627_);
lean_dec(v_x_624_);
v___x_650_ = lean_nat_add(v_x_617_, v___x_626_);
v_c_651_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_618_, v_v_619_, v___x_650_);
lean_dec(v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_k_620_);
lean_ctor_set(v___x_652_, 1, v_c_651_);
v___x_653_ = lean_nat_add(v_x_623_, v___x_626_);
lean_dec(v_x_623_);
v_j_654_ = lean_array_get_size(v_as_621_);
v_as_655_ = lean_array_push(v_as_621_, v___x_652_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_653_, v_as_655_, v_j_654_);
lean_dec(v___x_653_);
return v___x_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_x_657_, lean_object* v_keys_658_, lean_object* v_v_659_, lean_object* v_k_660_, lean_object* v_as_661_, lean_object* v_k_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_array_get_size(v_as_661_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_nat_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_array_fget_borrowed(v_as_661_, v___x_664_);
v___x_667_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_k_662_, v___x_666_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v___x_666_, v_k_662_);
v___x_669_ = lean_bool_not(v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_sub(v___x_663_, v___x_670_);
v___x_672_ = lean_array_fget_borrowed(v_as_661_, v___x_671_);
v___x_673_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v___x_672_, v_k_662_);
if (v___x_673_ == 0)
{
uint8_t v___x_674_; uint8_t v___x_675_; 
v___x_674_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_k_662_, v___x_672_);
v___x_675_ = lean_bool_not(v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v_as_661_, v_k_662_, v___x_664_, v___x_671_);
return v___x_676_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_lt(v___x_671_, v___x_663_);
if (v___x_677_ == 0)
{
lean_dec(v___x_671_);
lean_dec(v_k_660_);
lean_dec_ref(v_v_659_);
return v_as_661_;
}
else
{
lean_object* v___x_678_; lean_object* v_xs_x27_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc(v___x_672_);
v___x_678_ = lean_box(0);
v_xs_x27_679_ = lean_array_fset(v_as_661_, v___x_671_, v___x_678_);
v___x_680_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_672_);
v___x_681_ = lean_array_fset(v_xs_x27_679_, v___x_671_, v___x_680_);
lean_dec(v___x_671_);
return v___x_681_;
}
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v___x_671_);
v___x_682_ = lean_box(0);
v___x_683_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_682_);
v___x_684_ = lean_array_push(v_as_661_, v___x_683_);
return v___x_684_;
}
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_nat_dec_lt(v___x_664_, v___x_663_);
if (v___x_685_ == 0)
{
lean_dec(v_k_660_);
lean_dec_ref(v_v_659_);
return v_as_661_;
}
else
{
lean_object* v___x_686_; lean_object* v_xs_x27_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc(v___x_666_);
v___x_686_ = lean_box(0);
v_xs_x27_687_ = lean_array_fset(v_as_661_, v___x_664_, v___x_686_);
v___x_688_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_666_);
v___x_689_ = lean_array_fset(v_xs_x27_687_, v___x_664_, v___x_688_);
return v___x_689_;
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_as_692_; lean_object* v___x_693_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_690_);
v_as_692_ = lean_array_push(v_as_661_, v___x_691_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_664_, v_as_692_, v___x_663_);
return v___x_693_;
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_box(0);
v___x_695_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_694_);
v___x_696_ = lean_array_push(v_as_661_, v___x_695_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_keys_697_, lean_object* v_v_698_, lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
lean_object* v_vs_701_; lean_object* v_children_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_719_; 
v_vs_701_ = lean_ctor_get(v_x_700_, 0);
v_children_702_ = lean_ctor_get(v_x_700_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_700_);
if (v_isSharedCheck_719_ == 0)
{
v___x_704_ = v_x_700_;
v_isShared_705_ = v_isSharedCheck_719_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_children_702_);
lean_inc(v_vs_701_);
lean_dec(v_x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_719_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_array_get_size(v_keys_697_);
v___x_707_ = lean_nat_dec_lt(v_x_699_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_vs_701_, v_v_698_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_708_);
v___x_710_ = v___x_704_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_children_702_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
else
{
lean_object* v_k_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_c_715_; lean_object* v___x_717_; 
v_k_712_ = lean_array_fget_borrowed(v_keys_697_, v_x_699_);
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1));
lean_inc_n(v_k_712_, 2);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_k_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v_c_715_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_x_699_, v_keys_697_, v_v_698_, v_k_712_, v_children_702_, v___x_714_);
lean_dec_ref_known(v___x_714_, 2);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v_c_715_);
v___x_717_ = v___x_704_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_vs_701_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_c_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(lean_object* v_x_720_, lean_object* v_keys_721_, lean_object* v_v_722_, lean_object* v_k_723_, lean_object* v_x_724_){
_start:
{
lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_735_; 
v_snd_725_ = lean_ctor_get(v_x_724_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v_x_724_, 0);
lean_dec(v_unused_736_);
v___x_727_ = v_x_724_;
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_dec(v_x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_735_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v_c_731_; lean_object* v___x_733_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_x_720_, v___x_729_);
v_c_731_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_721_, v_v_722_, v___x_730_, v_snd_725_);
lean_dec(v___x_730_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_c_731_);
lean_ctor_set(v___x_727_, 0, v_k_723_);
v___x_733_ = v___x_727_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_k_723_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_c_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_737_, lean_object* v_keys_738_, lean_object* v_v_739_, lean_object* v_k_740_, lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_737_, v_keys_738_, v_v_739_, v_k_740_, v_x_741_);
lean_dec_ref(v_keys_738_);
lean_dec(v_x_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_keys_743_, lean_object* v_v_744_, lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_743_, v_v_744_, v_x_745_, v_x_746_);
lean_dec(v_x_745_);
lean_dec_ref(v_keys_743_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_748_, lean_object* v_keys_749_, lean_object* v_v_750_, lean_object* v_k_751_, lean_object* v_as_752_, lean_object* v_k_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_748_, v_keys_749_, v_v_750_, v_k_751_, v_as_752_, v_k_753_, v_x_754_, v_x_755_);
lean_dec_ref(v_k_753_);
lean_dec_ref(v_keys_749_);
lean_dec(v_x_748_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_x_757_, lean_object* v_keys_758_, lean_object* v_v_759_, lean_object* v_k_760_, lean_object* v_as_761_, lean_object* v_k_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_x_757_, v_keys_758_, v_v_759_, v_k_760_, v_as_761_, v_k_762_);
lean_dec_ref(v_k_762_);
lean_dec_ref(v_keys_758_);
lean_dec(v_x_757_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v_keys_764_, lean_object* v_v_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_764_, v_v_765_, v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_779_; 
v_val_770_ = lean_ctor_get(v_x_766_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_766_);
if (v_isSharedCheck_779_ == 0)
{
v___x_772_ = v_x_766_;
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v_x_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_764_, v_v_765_, v___x_774_, v_val_770_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v_keys_780_, lean_object* v_v_781_, lean_object* v_x_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_780_, v_v_781_, v_x_782_);
lean_dec_ref(v_keys_780_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_keys_784_, lean_object* v_v_785_, lean_object* v_x_786_, size_t v_x_787_, size_t v_x_788_, lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
lean_object* v_es_790_; size_t v___x_791_; size_t v___x_792_; lean_object* v_j_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_es_790_ = lean_ctor_get(v_x_786_, 0);
v___x_791_ = ((size_t)31ULL);
v___x_792_ = lean_usize_land(v_x_787_, v___x_791_);
v_j_793_ = lean_usize_to_nat(v___x_792_);
v___x_794_ = lean_array_get_size(v_es_790_);
v___x_795_ = lean_nat_dec_lt(v_j_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec(v_j_793_);
lean_dec(v_x_789_);
lean_dec_ref(v_v_785_);
return v_x_786_;
}
else
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_863_; 
lean_inc_ref(v_es_790_);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_x_786_, 0);
lean_dec(v_unused_864_);
v___x_797_ = v_x_786_;
v_isShared_798_ = v_isSharedCheck_863_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_x_786_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_863_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_v_799_; lean_object* v___x_800_; lean_object* v_xs_x27_801_; lean_object* v___y_803_; 
v_v_799_ = lean_array_fget(v_es_790_, v_j_793_);
v___x_800_ = lean_box(0);
v_xs_x27_801_ = lean_array_fset(v_es_790_, v_j_793_, v___x_800_);
switch(lean_obj_tag(v_v_799_))
{
case 0:
{
lean_object* v_key_808_; lean_object* v_val_809_; uint8_t v___x_810_; 
v_key_808_ = lean_ctor_get(v_v_799_, 0);
v_val_809_ = lean_ctor_get(v_v_799_, 1);
v___x_810_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_789_, v_key_808_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_box(0);
v___x_812_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_784_, v_v_785_, v___x_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_dec(v_x_789_);
v___y_803_ = v_v_799_;
goto v___jp_802_;
}
else
{
lean_object* v_val_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
lean_inc(v_val_809_);
lean_inc(v_key_808_);
lean_dec_ref_known(v_v_799_, 2);
v_val_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_821_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_val_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_808_, v_val_809_, v_x_789_, v_val_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v___y_803_ = v___x_819_;
goto v___jp_802_;
}
}
}
}
else
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_832_; 
lean_inc(v_val_809_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_v_799_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; lean_object* v_unused_834_; 
v_unused_833_ = lean_ctor_get(v_v_799_, 1);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_v_799_, 0);
lean_dec(v_unused_834_);
v___x_823_ = v_v_799_;
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_v_799_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_val_809_);
v___x_826_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_784_, v_v_785_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_827_; 
lean_del_object(v___x_823_);
lean_dec(v_x_789_);
v___x_827_ = lean_box(2);
v___y_803_ = v___x_827_;
goto v___jp_802_;
}
else
{
lean_object* v_val_828_; lean_object* v___x_830_; 
v_val_828_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v___x_826_, 1);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_val_828_);
lean_ctor_set(v___x_823_, 0, v_x_789_);
v___x_830_ = v___x_823_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_x_789_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_val_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v___y_803_ = v___x_830_;
goto v___jp_802_;
}
}
}
}
}
case 1:
{
lean_object* v_node_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_858_; 
v_node_835_ = lean_ctor_get(v_v_799_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_v_799_);
if (v_isSharedCheck_858_ == 0)
{
v___x_837_ = v_v_799_;
v_isShared_838_ = v_isSharedCheck_858_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_node_835_);
lean_dec(v_v_799_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_858_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v_newNode_843_; lean_object* v___x_844_; 
v___x_839_ = ((size_t)5ULL);
v___x_840_ = lean_usize_shift_right(v_x_787_, v___x_839_);
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_x_788_, v___x_841_);
v_newNode_843_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_784_, v_v_785_, v_node_835_, v___x_840_, v___x_842_, v_x_789_);
lean_inc_ref(v_newNode_843_);
v___x_844_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_846_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v_newNode_843_);
v___x_846_ = v___x_837_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_newNode_843_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v___y_803_ = v___x_846_;
goto v___jp_802_;
}
}
else
{
lean_object* v_val_848_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_newNode_843_);
lean_del_object(v___x_837_);
v_val_848_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v___x_844_, 1);
v_fst_849_ = lean_ctor_get(v_val_848_, 0);
v_snd_850_ = lean_ctor_get(v_val_848_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_val_848_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v_val_848_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_inc(v_fst_849_);
lean_dec(v_val_848_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_fst_849_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_snd_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
v___y_803_ = v___x_855_;
goto v___jp_802_;
}
}
}
}
}
default: 
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(0);
v___x_860_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_784_, v_v_785_, v___x_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_dec(v_x_789_);
v___y_803_ = v_v_799_;
goto v___jp_802_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_862_; 
v_val_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_val_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_x_789_);
lean_ctor_set(v___x_862_, 1, v_val_861_);
v___y_803_ = v___x_862_;
goto v___jp_802_;
}
}
}
v___jp_802_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_array_fset(v_xs_x27_801_, v_j_793_, v___y_803_);
lean_dec(v_j_793_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_804_);
v___x_806_ = v___x_797_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
else
{
lean_object* v_ks_865_; lean_object* v_vs_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_899_; 
v_ks_865_ = lean_ctor_get(v_x_786_, 0);
v_vs_866_ = lean_ctor_get(v_x_786_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_899_ == 0)
{
v___x_868_ = v_x_786_;
v_isShared_869_ = v_isSharedCheck_899_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_vs_866_);
lean_inc(v_ks_865_);
lean_dec(v_x_786_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_899_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; 
v___x_870_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(v_ks_865_, v_x_789_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_872_; 
if (v_isShared_869_ == 0)
{
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_ks_865_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_vs_866_);
v___x_872_ = v_reuseFailAlloc_877_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(0);
v___x_874_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_784_, v_v_785_, v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec(v_x_789_);
return v___x_872_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_876_; 
v_val_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v___x_872_, v_x_787_, v_x_788_, v_x_789_, v_val_875_);
return v___x_876_;
}
}
}
else
{
lean_object* v_val_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_898_; 
v_val_878_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_898_ == 0)
{
v___x_880_ = v___x_870_;
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_val_878_);
lean_dec(v___x_870_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_v_x27_882_; lean_object* v_keys_883_; lean_object* v_vals_884_; lean_object* v___x_886_; 
v_v_x27_882_ = lean_array_fget(v_vs_866_, v_val_878_);
lean_inc(v_val_878_);
v_keys_883_ = l_Array_eraseIdx___redArg(v_ks_865_, v_val_878_);
v_vals_884_ = l_Array_eraseIdx___redArg(v_vs_866_, v_val_878_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_v_x27_882_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_v_x27_882_);
v___x_886_ = v_reuseFailAlloc_897_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_784_, v_v_785_, v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_889_; 
lean_dec(v_x_789_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_vals_884_);
lean_ctor_set(v___x_868_, 0, v_keys_883_);
v___x_889_ = v___x_868_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_keys_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_vals_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v_val_891_; lean_object* v_keys_892_; lean_object* v_vals_893_; lean_object* v___x_895_; 
v_val_891_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___x_887_, 1);
v_keys_892_ = lean_array_push(v_keys_883_, v_x_789_);
v_vals_893_ = lean_array_push(v_vals_884_, v_val_891_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_vals_893_);
lean_ctor_set(v___x_868_, 0, v_keys_892_);
v___x_895_ = v___x_868_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_keys_892_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_vals_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_keys_900_, lean_object* v_v_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_2479__boxed_906_; size_t v_x_2480__boxed_907_; lean_object* v_res_908_; 
v_x_2479__boxed_906_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_x_2480__boxed_907_ = lean_unbox_usize(v_x_904_);
lean_dec(v_x_904_);
v_res_908_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_900_, v_v_901_, v_x_902_, v_x_2479__boxed_906_, v_x_2480__boxed_907_, v_x_905_);
lean_dec_ref(v_keys_900_);
return v_res_908_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_msg_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0);
v___x_912_ = lean_panic_fn_borrowed(v___x_911_, v_msg_910_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_916_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2));
v___x_917_ = lean_unsigned_to_nat(23u);
v___x_918_ = lean_unsigned_to_nat(166u);
v___x_919_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1));
v___x_920_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0));
v___x_921_ = l_mkPanicMessageWithDecl(v___x_920_, v___x_919_, v___x_918_, v___x_917_, v___x_916_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(lean_object* v_d_922_, lean_object* v_keys_923_, lean_object* v_v_924_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_925_ = lean_array_get_size(v_keys_923_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_nat_dec_eq(v___x_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v_k_929_; uint64_t v___x_930_; size_t v_h_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_928_ = lean_box(0);
v_k_929_ = lean_array_get_borrowed(v___x_928_, v_keys_923_, v___x_926_);
v___x_930_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_929_);
v_h_931_ = lean_uint64_to_usize(v___x_930_);
v___x_932_ = ((size_t)1ULL);
lean_inc(v_k_929_);
v___x_933_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_923_, v_v_924_, v_d_922_, v_h_931_, v___x_932_, v_k_929_);
return v___x_933_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_v_924_);
lean_dec_ref(v_d_922_);
v___x_934_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3);
v___x_935_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v___x_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_936_, lean_object* v_keys_937_, lean_object* v_v_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_d_936_, v_keys_937_, v_v_938_);
lean_dec_ref(v_keys_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_940_, lean_object* v_thm_941_){
_start:
{
lean_object* v_tree_942_; lean_object* v_erased_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_954_; 
v_tree_942_ = lean_ctor_get(v_x_940_, 0);
v_erased_943_ = lean_ctor_get(v_x_940_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_954_ == 0)
{
v___x_945_ = v_x_940_;
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_erased_943_);
lean_inc(v_tree_942_);
lean_dec(v_x_940_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_declName_947_; lean_object* v_keys_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v_declName_947_ = lean_ctor_get(v_thm_941_, 0);
lean_inc(v_declName_947_);
v_keys_948_ = lean_ctor_get(v_thm_941_, 2);
lean_inc_ref(v_keys_948_);
v___x_949_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_tree_942_, v_keys_948_, v_thm_941_);
lean_dec_ref(v_keys_948_);
v___x_950_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_erased_943_, v_declName_947_);
lean_dec(v_declName_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_950_);
lean_ctor_set(v___x_945_, 0, v___x_949_);
v___x_952_ = v___x_945_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v___y_955_){
_start:
{
lean_inc_ref(v___y_955_);
return v___y_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v___y_956_);
lean_dec_ref(v___y_956_);
return v_res_957_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_970_; lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___f_970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___f_971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_972_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3);
v___f_973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___f_973_);
lean_ctor_set(v___x_975_, 2, v___x_972_);
lean_ctor_set(v___x_975_, 3, v___f_971_);
lean_ctor_set(v___x_975_, 4, v___f_970_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_);
v___x_978_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(v_00_u03b2_985_, v_x_986_, v_x_987_);
lean_dec(v_x_987_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, size_t v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_990_, v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
size_t v_x_2848__boxed_998_; lean_object* v_res_999_; 
v_x_2848__boxed_998_ = lean_unbox_usize(v_x_996_);
lean_dec(v_x_996_);
v_res_999_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_994_, v_x_995_, v_x_2848__boxed_998_, v_x_997_);
lean_dec(v_x_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, size_t v_x_1002_, size_t v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_x_1001_, v_x_1002_, v_x_1003_, v_x_1004_, v_x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
size_t v_x_2859__boxed_1013_; size_t v_x_2860__boxed_1014_; lean_object* v_res_1015_; 
v_x_2859__boxed_1013_ = lean_unbox_usize(v_x_1009_);
lean_dec(v_x_1009_);
v_x_2860__boxed_1014_ = lean_unbox_usize(v_x_1010_);
lean_dec(v_x_1010_);
v_res_1015_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(v_00_u03b2_1007_, v_x_1008_, v_x_2859__boxed_1013_, v_x_2860__boxed_1014_, v_x_1011_, v_x_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_x_1016_, lean_object* v_keys_1017_, lean_object* v_v_1018_, lean_object* v_k_1019_, lean_object* v_as_1020_, lean_object* v_k_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_1016_, v_keys_1017_, v_v_1018_, v_k_1019_, v_as_1020_, v_k_1021_, v_x_1022_, v_x_1023_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_x_1027_, lean_object* v_keys_1028_, lean_object* v_v_1029_, lean_object* v_k_1030_, lean_object* v_as_1031_, lean_object* v_k_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_x_1027_, v_keys_1028_, v_v_1029_, v_k_1030_, v_as_1031_, v_k_1032_, v_x_1033_, v_x_1034_, v_x_1035_, v_x_1036_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_keys_1028_);
lean_dec(v_x_1027_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1038_, lean_object* v_n_1039_, lean_object* v_k_1040_, lean_object* v_v_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(v_n_1039_, v_k_1040_, v_v_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_1043_, size_t v_depth_1044_, lean_object* v_keys_1045_, lean_object* v_vals_1046_, lean_object* v_heq_1047_, lean_object* v_i_1048_, lean_object* v_entries_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(v_depth_1044_, v_keys_1045_, v_vals_1046_, v_i_1048_, v_entries_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_depth_1052_, lean_object* v_keys_1053_, lean_object* v_vals_1054_, lean_object* v_heq_1055_, lean_object* v_i_1056_, lean_object* v_entries_1057_){
_start:
{
size_t v_depth_boxed_1058_; lean_object* v_res_1059_; 
v_depth_boxed_1058_ = lean_unbox_usize(v_depth_1052_);
lean_dec(v_depth_1052_);
v_res_1059_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12(v_00_u03b2_1051_, v_depth_boxed_1058_, v_keys_1053_, v_vals_1054_, v_heq_1055_, v_i_1056_, v_entries_1057_);
lean_dec_ref(v_vals_1054_);
lean_dec_ref(v_keys_1053_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(v_x_1061_, v_x_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_getExtTheorems___lam__0(lean_object* v_x1_1066_, lean_object* v_x2_1067_){
_start:
{
lean_object* v_priority_1068_; lean_object* v_priority_1069_; uint8_t v___x_1070_; 
v_priority_1068_ = lean_ctor_get(v_x1_1066_, 1);
v_priority_1069_ = lean_ctor_get(v_x2_1067_, 1);
v___x_1070_ = lean_nat_dec_lt(v_priority_1068_, v_priority_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(lean_object* v_x1_1071_, lean_object* v_x2_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Lean_Meta_Ext_getExtTheorems___lam__0(v_x1_1071_, v_x2_1072_);
lean_dec_ref(v_x2_1072_);
lean_dec_ref(v_x1_1071_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__1(lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v_x1_1078_, lean_object* v_x2_1079_){
_start:
{
lean_object* v_erased_1080_; lean_object* v_declName_1081_; uint8_t v___x_1082_; uint8_t v___x_1083_; 
v_erased_1080_ = lean_ctor_get(v___x_1075_, 1);
lean_inc_ref(v_erased_1080_);
lean_dec_ref(v___x_1075_);
v_declName_1081_ = lean_ctor_get(v_x2_1079_, 0);
lean_inc(v_declName_1081_);
v___x_1082_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1076_, v___x_1077_, v_erased_1080_, v_declName_1081_);
v___x_1083_ = lean_bool_not(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v_x2_1079_);
return v_x1_1078_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_array_push(v_x1_1078_, v_x2_1079_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object* v_ty_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_env_1114_; lean_object* v___x_1115_; lean_object* v_ext_1116_; lean_object* v_toEnvExtension_1117_; lean_object* v_asyncMode_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v_tree_1121_; lean_object* v___x_1122_; 
v___x_1113_ = lean_st_ref_get(v_a_1111_);
v_env_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1114_);
lean_dec(v___x_1113_);
v___x_1115_ = l_Lean_Meta_Ext_extExtension;
v_ext_1116_ = lean_ctor_get(v___x_1115_, 1);
v_toEnvExtension_1117_ = lean_ctor_get(v_ext_1116_, 0);
v_asyncMode_1118_ = lean_ctor_get(v_toEnvExtension_1117_, 2);
v___x_1119_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1120_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1119_, v___x_1115_, v_env_1114_, v_asyncMode_1118_);
v_tree_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc_ref(v_tree_1121_);
v___x_1122_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_tree_1121_, v_ty_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec_ref(v_tree_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1152_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1152_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1152_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___f_1127_; lean_object* v___y_1129_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___f_1127_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__0));
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_array_get_size(v_a_1123_);
v___x_1139_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__10));
v___x_1141_ = lean_nat_dec_lt(v___x_1137_, v___x_1138_);
if (v___x_1141_ == 0)
{
lean_dec(v_a_1123_);
lean_dec(v___x_1120_);
v___y_1129_ = v___x_1139_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___f_1144_; uint8_t v___x_1145_; 
v___x_1142_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__11));
v___x_1143_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__12));
v___f_1144_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_getExtTheorems___lam__1), 5, 3);
lean_closure_set(v___f_1144_, 0, v___x_1120_);
lean_closure_set(v___f_1144_, 1, v___x_1142_);
lean_closure_set(v___f_1144_, 2, v___x_1143_);
v___x_1145_ = lean_nat_dec_le(v___x_1138_, v___x_1138_);
if (v___x_1145_ == 0)
{
if (v___x_1141_ == 0)
{
lean_dec_ref(v___f_1144_);
lean_dec(v_a_1123_);
v___y_1129_ = v___x_1139_;
goto v___jp_1128_;
}
else
{
size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = lean_usize_of_nat(v___x_1138_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1140_, v___f_1144_, v_a_1123_, v___x_1146_, v___x_1147_, v___x_1139_);
v___y_1129_ = v___x_1148_;
goto v___jp_1128_;
}
}
else
{
size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = lean_usize_of_nat(v___x_1138_);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1140_, v___f_1144_, v_a_1123_, v___x_1149_, v___x_1150_, v___x_1139_);
v___y_1129_ = v___x_1151_;
goto v___jp_1128_;
}
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_array_get_size(v___y_1129_);
v___x_1132_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(lean_box(0), v___f_1127_, v___y_1129_, v___x_1130_, v___x_1131_);
v___x_1133_ = l_Array_reverse___redArg(v___x_1132_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1133_);
v___x_1135_ = v___x_1125_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_dec(v___x_1120_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___boxed(lean_object* v_ty_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_Ext_getExtTheorems(v_ty_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
lean_object* v_ks_1164_; lean_object* v_vs_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1189_; 
v_ks_1164_ = lean_ctor_get(v_x_1160_, 0);
v_vs_1165_ = lean_ctor_get(v_x_1160_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_x_1160_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1167_ = v_x_1160_;
v_isShared_1168_ = v_isSharedCheck_1189_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_vs_1165_);
lean_inc(v_ks_1164_);
lean_dec(v_x_1160_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1189_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_array_get_size(v_ks_1164_);
v___x_1170_ = lean_nat_dec_lt(v_x_1161_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
lean_dec(v_x_1161_);
v___x_1171_ = lean_array_push(v_ks_1164_, v_x_1162_);
v___x_1172_ = lean_array_push(v_vs_1165_, v_x_1163_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1172_);
lean_ctor_set(v___x_1167_, 0, v___x_1171_);
v___x_1174_ = v___x_1167_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
else
{
lean_object* v_k_x27_1176_; uint8_t v___x_1177_; 
v_k_x27_1176_ = lean_array_fget_borrowed(v_ks_1164_, v_x_1161_);
v___x_1177_ = lean_name_eq(v_x_1162_, v_k_x27_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1179_; 
if (v_isShared_1168_ == 0)
{
v___x_1179_ = v___x_1167_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_ks_1164_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_vs_1165_);
v___x_1179_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_nat_add(v_x_1161_, v___x_1180_);
lean_dec(v_x_1161_);
v_x_1160_ = v___x_1179_;
v_x_1161_ = v___x_1181_;
goto _start;
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = lean_array_fset(v_ks_1164_, v_x_1161_, v_x_1162_);
v___x_1185_ = lean_array_fset(v_vs_1165_, v_x_1161_, v_x_1163_);
lean_dec(v_x_1161_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1185_);
lean_ctor_set(v___x_1167_, 0, v___x_1184_);
v___x_1187_ = v___x_1167_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1190_, lean_object* v_k_1191_, lean_object* v_v_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1190_, v___x_1193_, v_k_1191_, v_v_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(lean_object* v_x_1196_, size_t v_x_1197_, size_t v_x_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
if (lean_obj_tag(v_x_1196_) == 0)
{
lean_object* v_es_1201_; size_t v___x_1202_; size_t v___x_1203_; lean_object* v_j_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_es_1201_ = lean_ctor_get(v_x_1196_, 0);
v___x_1202_ = ((size_t)31ULL);
v___x_1203_ = lean_usize_land(v_x_1197_, v___x_1202_);
v_j_1204_ = lean_usize_to_nat(v___x_1203_);
v___x_1205_ = lean_array_get_size(v_es_1201_);
v___x_1206_ = lean_nat_dec_lt(v_j_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_dec(v_j_1204_);
lean_dec(v_x_1200_);
lean_dec(v_x_1199_);
return v_x_1196_;
}
else
{
lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1245_; 
lean_inc_ref(v_es_1201_);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_x_1196_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_x_1196_, 0);
lean_dec(v_unused_1246_);
v___x_1208_ = v_x_1196_;
v_isShared_1209_ = v_isSharedCheck_1245_;
goto v_resetjp_1207_;
}
else
{
lean_dec(v_x_1196_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1245_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_v_1210_; lean_object* v___x_1211_; lean_object* v_xs_x27_1212_; lean_object* v___y_1214_; 
v_v_1210_ = lean_array_fget(v_es_1201_, v_j_1204_);
v___x_1211_ = lean_box(0);
v_xs_x27_1212_ = lean_array_fset(v_es_1201_, v_j_1204_, v___x_1211_);
switch(lean_obj_tag(v_v_1210_))
{
case 0:
{
lean_object* v_key_1219_; lean_object* v_val_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1230_; 
v_key_1219_ = lean_ctor_get(v_v_1210_, 0);
v_val_1220_ = lean_ctor_get(v_v_1210_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_v_1210_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1222_ = v_v_1210_;
v_isShared_1223_ = v_isSharedCheck_1230_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_val_1220_);
lean_inc(v_key_1219_);
lean_dec(v_v_1210_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1230_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
uint8_t v___x_1224_; 
v___x_1224_ = lean_name_eq(v_x_1199_, v_key_1219_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_del_object(v___x_1222_);
v___x_1225_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1219_, v_val_1220_, v_x_1199_, v_x_1200_);
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
v___y_1214_ = v___x_1226_;
goto v___jp_1213_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_val_1220_);
lean_dec(v_key_1219_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v_x_1200_);
lean_ctor_set(v___x_1222_, 0, v_x_1199_);
v___x_1228_ = v___x_1222_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_x_1199_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_x_1200_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
v___y_1214_ = v___x_1228_;
goto v___jp_1213_;
}
}
}
}
case 1:
{
lean_object* v_node_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1243_; 
v_node_1231_ = lean_ctor_get(v_v_1210_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_v_1210_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1233_ = v_v_1210_;
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_node_1231_);
lean_dec(v_v_1210_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1243_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
size_t v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1235_ = ((size_t)5ULL);
v___x_1236_ = lean_usize_shift_right(v_x_1197_, v___x_1235_);
v___x_1237_ = ((size_t)1ULL);
v___x_1238_ = lean_usize_add(v_x_1198_, v___x_1237_);
v___x_1239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_node_1231_, v___x_1236_, v___x_1238_, v_x_1199_, v_x_1200_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1239_);
v___x_1241_ = v___x_1233_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
v___y_1214_ = v___x_1241_;
goto v___jp_1213_;
}
}
}
default: 
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_x_1199_);
lean_ctor_set(v___x_1244_, 1, v_x_1200_);
v___y_1214_ = v___x_1244_;
goto v___jp_1213_;
}
}
v___jp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_array_fset(v_xs_x27_1212_, v_j_1204_, v___y_1214_);
lean_dec(v_j_1204_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1215_);
v___x_1217_ = v___x_1208_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
else
{
lean_object* v_ks_1247_; lean_object* v_vs_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1268_; 
v_ks_1247_ = lean_ctor_get(v_x_1196_, 0);
v_vs_1248_ = lean_ctor_get(v_x_1196_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_1196_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1250_ = v_x_1196_;
v_isShared_1251_ = v_isSharedCheck_1268_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_vs_1248_);
lean_inc(v_ks_1247_);
lean_dec(v_x_1196_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1268_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_ks_1247_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_vs_1248_);
v___x_1253_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v_newNode_1254_; uint8_t v___y_1256_; size_t v___x_1262_; uint8_t v___x_1263_; 
v_newNode_1254_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v___x_1253_, v_x_1199_, v_x_1200_);
v___x_1262_ = ((size_t)7ULL);
v___x_1263_ = lean_usize_dec_le(v___x_1262_, v_x_1198_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1254_);
v___x_1265_ = lean_unsigned_to_nat(4u);
v___x_1266_ = lean_nat_dec_lt(v___x_1264_, v___x_1265_);
lean_dec(v___x_1264_);
v___y_1256_ = v___x_1266_;
goto v___jp_1255_;
}
else
{
v___y_1256_ = v___x_1263_;
goto v___jp_1255_;
}
v___jp_1255_:
{
if (v___y_1256_ == 0)
{
lean_object* v_ks_1257_; lean_object* v_vs_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_ks_1257_ = lean_ctor_get(v_newNode_1254_, 0);
lean_inc_ref(v_ks_1257_);
v_vs_1258_ = lean_ctor_get(v_newNode_1254_, 1);
lean_inc_ref(v_vs_1258_);
lean_dec_ref(v_newNode_1254_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0);
v___x_1261_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_x_1198_, v_ks_1257_, v_vs_1258_, v___x_1259_, v___x_1260_);
lean_dec_ref(v_vs_1258_);
lean_dec_ref(v_ks_1257_);
return v___x_1261_;
}
else
{
return v_newNode_1254_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_1269_, lean_object* v_keys_1270_, lean_object* v_vals_1271_, lean_object* v_i_1272_, lean_object* v_entries_1273_){
_start:
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = lean_array_get_size(v_keys_1270_);
v___x_1275_ = lean_nat_dec_lt(v_i_1272_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec(v_i_1272_);
return v_entries_1273_;
}
else
{
lean_object* v_k_1276_; lean_object* v_v_1277_; uint64_t v___y_1279_; 
v_k_1276_ = lean_array_fget_borrowed(v_keys_1270_, v_i_1272_);
v_v_1277_ = lean_array_fget_borrowed(v_vals_1271_, v_i_1272_);
if (lean_obj_tag(v_k_1276_) == 0)
{
uint64_t v___x_1290_; 
v___x_1290_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1279_ = v___x_1290_;
goto v___jp_1278_;
}
else
{
uint64_t v_hash_1291_; 
v_hash_1291_ = lean_ctor_get_uint64(v_k_1276_, sizeof(void*)*2);
v___y_1279_ = v_hash_1291_;
goto v___jp_1278_;
}
v___jp_1278_:
{
size_t v_h_1280_; size_t v___x_1281_; lean_object* v___x_1282_; size_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; size_t v_h_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_h_1280_ = lean_uint64_to_usize(v___y_1279_);
v___x_1281_ = ((size_t)5ULL);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_sub(v_depth_1269_, v___x_1283_);
v___x_1285_ = lean_usize_mul(v___x_1281_, v___x_1284_);
v_h_1286_ = lean_usize_shift_right(v_h_1280_, v___x_1285_);
v___x_1287_ = lean_nat_add(v_i_1272_, v___x_1282_);
lean_dec(v_i_1272_);
lean_inc(v_v_1277_);
lean_inc(v_k_1276_);
v___x_1288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_entries_1273_, v_h_1286_, v_depth_1269_, v_k_1276_, v_v_1277_);
v_i_1272_ = v___x_1287_;
v_entries_1273_ = v___x_1288_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1292_, lean_object* v_keys_1293_, lean_object* v_vals_1294_, lean_object* v_i_1295_, lean_object* v_entries_1296_){
_start:
{
size_t v_depth_boxed_1297_; lean_object* v_res_1298_; 
v_depth_boxed_1297_ = lean_unbox_usize(v_depth_1292_);
lean_dec(v_depth_1292_);
v_res_1298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1297_, v_keys_1293_, v_vals_1294_, v_i_1295_, v_entries_1296_);
lean_dec_ref(v_vals_1294_);
lean_dec_ref(v_keys_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
size_t v_x_363__boxed_1304_; size_t v_x_364__boxed_1305_; lean_object* v_res_1306_; 
v_x_363__boxed_1304_ = lean_unbox_usize(v_x_1300_);
lean_dec(v_x_1300_);
v_x_364__boxed_1305_ = lean_unbox_usize(v_x_1301_);
lean_dec(v_x_1301_);
v_res_1306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1299_, v_x_363__boxed_1304_, v_x_364__boxed_1305_, v_x_1302_, v_x_1303_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_){
_start:
{
uint64_t v___y_1311_; 
if (lean_obj_tag(v_x_1308_) == 0)
{
uint64_t v___x_1315_; 
v___x_1315_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1311_ = v___x_1315_;
goto v___jp_1310_;
}
else
{
uint64_t v_hash_1316_; 
v_hash_1316_ = lean_ctor_get_uint64(v_x_1308_, sizeof(void*)*2);
v___y_1311_ = v_hash_1316_;
goto v___jp_1310_;
}
v___jp_1310_:
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_uint64_to_usize(v___y_1311_);
v___x_1313_ = ((size_t)1ULL);
v___x_1314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1307_, v___x_1312_, v___x_1313_, v_x_1308_, v_x_1309_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object* v_d_1317_, lean_object* v_declName_1318_){
_start:
{
lean_object* v_tree_1319_; lean_object* v_erased_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1329_; 
v_tree_1319_ = lean_ctor_get(v_d_1317_, 0);
v_erased_1320_ = lean_ctor_get(v_d_1317_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_d_1317_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1322_ = v_d_1317_;
v_isShared_1323_ = v_isSharedCheck_1329_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_erased_1320_);
lean_inc(v_tree_1319_);
lean_dec(v_d_1317_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1329_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_erased_1320_, v_declName_1318_, v___x_1324_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1325_);
v___x_1327_ = v___x_1322_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_tree_1319_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0(lean_object* v_00_u03b2_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_x_1331_, v_x_1332_, v_x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(lean_object* v_00_u03b2_1335_, lean_object* v_x_1336_, size_t v_x_1337_, size_t v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1336_, v_x_1337_, v_x_1338_, v_x_1339_, v_x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
size_t v_x_568__boxed_1348_; size_t v_x_569__boxed_1349_; lean_object* v_res_1350_; 
v_x_568__boxed_1348_ = lean_unbox_usize(v_x_1344_);
lean_dec(v_x_1344_);
v_x_569__boxed_1349_ = lean_unbox_usize(v_x_1345_);
lean_dec(v_x_1345_);
v_res_1350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(v_00_u03b2_1342_, v_x_1343_, v_x_568__boxed_1348_, v_x_569__boxed_1349_, v_x_1346_, v_x_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1351_, lean_object* v_n_1352_, lean_object* v_k_1353_, lean_object* v_v_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v_n_1352_, v_k_1353_, v_v_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1356_, size_t v_depth_1357_, lean_object* v_keys_1358_, lean_object* v_vals_1359_, lean_object* v_heq_1360_, lean_object* v_i_1361_, lean_object* v_entries_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_1357_, v_keys_1358_, v_vals_1359_, v_i_1361_, v_entries_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1364_, lean_object* v_depth_1365_, lean_object* v_keys_1366_, lean_object* v_vals_1367_, lean_object* v_heq_1368_, lean_object* v_i_1369_, lean_object* v_entries_1370_){
_start:
{
size_t v_depth_boxed_1371_; lean_object* v_res_1372_; 
v_depth_boxed_1371_ = lean_unbox_usize(v_depth_1365_);
lean_dec(v_depth_1365_);
v_res_1372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(v_00_u03b2_1364_, v_depth_boxed_1371_, v_keys_1366_, v_vals_1367_, v_heq_1368_, v_i_1369_, v_entries_1370_);
lean_dec_ref(v_vals_1367_);
lean_dec_ref(v_keys_1366_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1374_, v_x_1375_, v_x_1376_, v_x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(lean_object* v_declName_1379_, uint8_t v_x1_1380_, lean_object* v_x2_1381_){
_start:
{
if (v_x1_1380_ == 0)
{
lean_object* v_declName_1382_; uint8_t v___x_1383_; 
v_declName_1382_ = lean_ctor_get(v_x2_1381_, 0);
v___x_1383_ = lean_name_eq(v_declName_1382_, v_declName_1379_);
return v___x_1383_;
}
else
{
return v_x1_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(lean_object* v_declName_1384_, lean_object* v_x1_1385_, lean_object* v_x2_1386_){
_start:
{
uint8_t v_x1_1192__boxed_1387_; uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_x1_1192__boxed_1387_ = lean_unbox(v_x1_1385_);
v_res_1388_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(v_declName_1384_, v_x1_1192__boxed_1387_, v_x2_1386_);
lean_dec_ref(v_x2_1386_);
lean_dec(v_declName_1384_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(lean_object* v_f_1390_, lean_object* v_as_1391_, size_t v_i_1392_, size_t v_stop_1393_, lean_object* v_b_1394_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_eq(v_i_1392_, v_stop_1393_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; 
v___x_1396_ = lean_array_uget_borrowed(v_as_1391_, v_i_1392_);
lean_inc(v_f_1390_);
lean_inc(v___x_1396_);
v___x_1397_ = lean_apply_2(v_f_1390_, v_b_1394_, v___x_1396_);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1392_, v___x_1398_);
v_i_1392_ = v___x_1399_;
v_b_1394_ = v___x_1397_;
goto _start;
}
else
{
lean_dec(v_f_1390_);
return v_b_1394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg___boxed(lean_object* v_f_1401_, lean_object* v_as_1402_, lean_object* v_i_1403_, lean_object* v_stop_1404_, lean_object* v_b_1405_){
_start:
{
size_t v_i_boxed_1406_; size_t v_stop_boxed_1407_; lean_object* v_res_1408_; 
v_i_boxed_1406_ = lean_unbox_usize(v_i_1403_);
lean_dec(v_i_1403_);
v_stop_boxed_1407_ = lean_unbox_usize(v_stop_1404_);
lean_dec(v_stop_1404_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1401_, v_as_1402_, v_i_boxed_1406_, v_stop_boxed_1407_, v_b_1405_);
lean_dec_ref(v_as_1402_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(lean_object* v_f_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v_vs_1412_; lean_object* v_children_1413_; lean_object* v___x_1414_; lean_object* v_s_1416_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_vs_1412_ = lean_ctor_get(v_x_1411_, 0);
v_children_1413_ = lean_ctor_get(v_x_1411_, 1);
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_array_get_size(v_vs_1412_);
v___x_1427_ = lean_nat_dec_lt(v___x_1414_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1428_ = lean_array_get_size(v_children_1413_);
v___x_1429_ = lean_nat_dec_lt(v___x_1414_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_dec(v_f_1409_);
return v_x_1410_;
}
else
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_nat_dec_le(v___x_1428_, v___x_1428_);
if (v___x_1430_ == 0)
{
if (v___x_1429_ == 0)
{
lean_dec(v_f_1409_);
return v_x_1410_;
}
else
{
size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = ((size_t)0ULL);
v___x_1432_ = lean_usize_of_nat(v___x_1428_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1409_, v_children_1413_, v___x_1431_, v___x_1432_, v_x_1410_);
return v___x_1433_;
}
}
else
{
size_t v___x_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = lean_usize_of_nat(v___x_1428_);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1409_, v_children_1413_, v___x_1434_, v___x_1435_, v_x_1410_);
return v___x_1436_;
}
}
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_le(v___x_1426_, v___x_1426_);
if (v___x_1437_ == 0)
{
if (v___x_1427_ == 0)
{
v_s_1416_ = v_x_1410_;
goto v___jp_1415_;
}
else
{
size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = ((size_t)0ULL);
v___x_1439_ = lean_usize_of_nat(v___x_1426_);
lean_inc(v_f_1409_);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1409_, v_vs_1412_, v___x_1438_, v___x_1439_, v_x_1410_);
v_s_1416_ = v___x_1440_;
goto v___jp_1415_;
}
}
else
{
size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = lean_usize_of_nat(v___x_1426_);
lean_inc(v_f_1409_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1409_, v_vs_1412_, v___x_1441_, v___x_1442_, v_x_1410_);
v_s_1416_ = v___x_1443_;
goto v___jp_1415_;
}
}
v___jp_1415_:
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = lean_array_get_size(v_children_1413_);
v___x_1418_ = lean_nat_dec_lt(v___x_1414_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec(v_f_1409_);
return v_s_1416_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_le(v___x_1417_, v___x_1417_);
if (v___x_1419_ == 0)
{
if (v___x_1418_ == 0)
{
lean_dec(v_f_1409_);
return v_s_1416_;
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1417_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1409_, v_children_1413_, v___x_1420_, v___x_1421_, v_s_1416_);
return v___x_1422_;
}
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1417_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1409_, v_children_1413_, v___x_1423_, v___x_1424_, v_s_1416_);
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(lean_object* v_f_1444_, lean_object* v_as_1445_, size_t v_i_1446_, size_t v_stop_1447_, lean_object* v_b_1448_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v_snd_1451_; lean_object* v___x_1452_; size_t v___x_1453_; size_t v___x_1454_; 
v___x_1450_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
v_snd_1451_ = lean_ctor_get(v___x_1450_, 1);
lean_inc(v_f_1444_);
v___x_1452_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1444_, v_b_1448_, v_snd_1451_);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1446_, v___x_1453_);
v_i_1446_ = v___x_1454_;
v_b_1448_ = v___x_1452_;
goto _start;
}
else
{
lean_dec(v_f_1444_);
return v_b_1448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_f_1456_, lean_object* v_as_1457_, lean_object* v_i_1458_, lean_object* v_stop_1459_, lean_object* v_b_1460_){
_start:
{
size_t v_i_boxed_1461_; size_t v_stop_boxed_1462_; lean_object* v_res_1463_; 
v_i_boxed_1461_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_stop_boxed_1462_ = lean_unbox_usize(v_stop_1459_);
lean_dec(v_stop_1459_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1456_, v_as_1457_, v_i_boxed_1461_, v_stop_boxed_1462_, v_b_1460_);
lean_dec_ref(v_as_1457_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg___boxed(lean_object* v_f_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1464_, v_x_1465_, v_x_1466_);
lean_dec_ref(v_x_1466_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(lean_object* v___f_1468_, uint8_t v_s_1469_, lean_object* v_x_1470_, lean_object* v_t_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_box(v_s_1469_);
v___x_1473_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v___f_1468_, v___x_1472_, v_t_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed(lean_object* v___f_1474_, lean_object* v_s_1475_, lean_object* v_x_1476_, lean_object* v_t_1477_){
_start:
{
uint8_t v_s_boxed_1478_; lean_object* v_res_1479_; 
v_s_boxed_1478_ = lean_unbox(v_s_1475_);
v_res_1479_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(v___f_1474_, v_s_boxed_1478_, v_x_1476_, v_t_1477_);
lean_dec_ref(v_t_1477_);
lean_dec(v_x_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(lean_object* v_keys_1480_, lean_object* v_i_1481_, lean_object* v_k_1482_){
_start:
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_array_get_size(v_keys_1480_);
v___x_1484_ = lean_nat_dec_lt(v_i_1481_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_dec(v_i_1481_);
return v___x_1484_;
}
else
{
lean_object* v_k_x27_1485_; uint8_t v___x_1486_; 
v_k_x27_1485_ = lean_array_fget_borrowed(v_keys_1480_, v_i_1481_);
v___x_1486_ = lean_name_eq(v_k_1482_, v_k_x27_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_add(v_i_1481_, v___x_1487_);
lean_dec(v_i_1481_);
v_i_1481_ = v___x_1488_;
goto _start;
}
else
{
lean_dec(v_i_1481_);
return v___x_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1490_, lean_object* v_i_1491_, lean_object* v_k_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1490_, v_i_1491_, v_k_1492_);
lean_dec(v_k_1492_);
lean_dec_ref(v_keys_1490_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(lean_object* v_x_1495_, size_t v_x_1496_, lean_object* v_x_1497_){
_start:
{
if (lean_obj_tag(v_x_1495_) == 0)
{
lean_object* v_es_1498_; lean_object* v___x_1499_; size_t v___x_1500_; size_t v___x_1501_; lean_object* v_j_1502_; lean_object* v___x_1503_; 
v_es_1498_ = lean_ctor_get(v_x_1495_, 0);
v___x_1499_ = lean_box(2);
v___x_1500_ = ((size_t)31ULL);
v___x_1501_ = lean_usize_land(v_x_1496_, v___x_1500_);
v_j_1502_ = lean_usize_to_nat(v___x_1501_);
v___x_1503_ = lean_array_get_borrowed(v___x_1499_, v_es_1498_, v_j_1502_);
lean_dec(v_j_1502_);
switch(lean_obj_tag(v___x_1503_))
{
case 0:
{
lean_object* v_key_1504_; uint8_t v___x_1505_; 
v_key_1504_ = lean_ctor_get(v___x_1503_, 0);
v___x_1505_ = lean_name_eq(v_x_1497_, v_key_1504_);
return v___x_1505_;
}
case 1:
{
lean_object* v_node_1506_; size_t v___x_1507_; size_t v___x_1508_; 
v_node_1506_ = lean_ctor_get(v___x_1503_, 0);
v___x_1507_ = ((size_t)5ULL);
v___x_1508_ = lean_usize_shift_right(v_x_1496_, v___x_1507_);
v_x_1495_ = v_node_1506_;
v_x_1496_ = v___x_1508_;
goto _start;
}
default: 
{
uint8_t v___x_1510_; 
v___x_1510_ = 0;
return v___x_1510_;
}
}
}
else
{
lean_object* v_ks_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_ks_1511_ = lean_ctor_get(v_x_1495_, 0);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_ks_1511_, v___x_1512_, v_x_1497_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
size_t v_x_1318__boxed_1517_; uint8_t v_res_1518_; lean_object* v_r_1519_; 
v_x_1318__boxed_1517_ = lean_unbox_usize(v_x_1515_);
lean_dec(v_x_1515_);
v_res_1518_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1514_, v_x_1318__boxed_1517_, v_x_1516_);
lean_dec(v_x_1516_);
lean_dec_ref(v_x_1514_);
v_r_1519_ = lean_box(v_res_1518_);
return v_r_1519_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
uint64_t v___y_1523_; 
if (lean_obj_tag(v_x_1521_) == 0)
{
uint64_t v___x_1526_; 
v___x_1526_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1523_ = v___x_1526_;
goto v___jp_1522_;
}
else
{
uint64_t v_hash_1527_; 
v_hash_1527_ = lean_ctor_get_uint64(v_x_1521_, sizeof(void*)*2);
v___y_1523_ = v_hash_1527_;
goto v___jp_1522_;
}
v___jp_1522_:
{
size_t v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = lean_uint64_to_usize(v___y_1523_);
v___x_1525_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1520_, v___x_1524_, v_x_1521_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_res_1530_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1528_, v_x_1529_);
lean_dec(v_x_1529_);
lean_dec_ref(v_x_1528_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(lean_object* v_f_1532_, lean_object* v_keys_1533_, lean_object* v_vals_1534_, lean_object* v_i_1535_, lean_object* v_acc_1536_){
_start:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = lean_array_get_size(v_keys_1533_);
v___x_1538_ = lean_nat_dec_lt(v_i_1535_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec(v_i_1535_);
lean_dec(v_f_1532_);
return v_acc_1536_;
}
else
{
lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_k_1539_ = lean_array_fget_borrowed(v_keys_1533_, v_i_1535_);
v_v_1540_ = lean_array_fget_borrowed(v_vals_1534_, v_i_1535_);
lean_inc(v_f_1532_);
lean_inc(v_v_1540_);
lean_inc(v_k_1539_);
v___x_1541_ = lean_apply_3(v_f_1532_, v_acc_1536_, v_k_1539_, v_v_1540_);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = lean_nat_add(v_i_1535_, v___x_1542_);
lean_dec(v_i_1535_);
v_i_1535_ = v___x_1543_;
v_acc_1536_ = v___x_1541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_1545_, lean_object* v_keys_1546_, lean_object* v_vals_1547_, lean_object* v_i_1548_, lean_object* v_acc_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1545_, v_keys_1546_, v_vals_1547_, v_i_1548_, v_acc_1549_);
lean_dec_ref(v_vals_1547_);
lean_dec_ref(v_keys_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(lean_object* v_f_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
if (lean_obj_tag(v_x_1552_) == 0)
{
lean_object* v_es_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_es_1554_ = lean_ctor_get(v_x_1552_, 0);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_get_size(v_es_1554_);
v___x_1557_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec(v_f_1551_);
return v_x_1553_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_nat_dec_le(v___x_1556_, v___x_1556_);
if (v___x_1558_ == 0)
{
if (v___x_1557_ == 0)
{
lean_dec(v_f_1551_);
return v_x_1553_;
}
else
{
size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = lean_usize_of_nat(v___x_1556_);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1551_, v_es_1554_, v___x_1559_, v___x_1560_, v_x_1553_);
return v___x_1561_;
}
}
else
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_of_nat(v___x_1556_);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1551_, v_es_1554_, v___x_1562_, v___x_1563_, v_x_1553_);
return v___x_1564_;
}
}
}
else
{
lean_object* v_ks_1565_; lean_object* v_vs_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_ks_1565_ = lean_ctor_get(v_x_1552_, 0);
v_vs_1566_ = lean_ctor_get(v_x_1552_, 1);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1551_, v_ks_1565_, v_vs_1566_, v___x_1567_, v_x_1553_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1569_, lean_object* v_as_1570_, size_t v_i_1571_, size_t v_stop_1572_, lean_object* v_b_1573_){
_start:
{
lean_object* v___y_1575_; uint8_t v___x_1579_; 
v___x_1579_ = lean_usize_dec_eq(v_i_1571_, v_stop_1572_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_array_uget_borrowed(v_as_1570_, v_i_1571_);
switch(lean_obj_tag(v___x_1580_))
{
case 0:
{
lean_object* v_key_1581_; lean_object* v_val_1582_; lean_object* v___x_1583_; 
v_key_1581_ = lean_ctor_get(v___x_1580_, 0);
v_val_1582_ = lean_ctor_get(v___x_1580_, 1);
lean_inc(v_f_1569_);
lean_inc(v_val_1582_);
lean_inc(v_key_1581_);
v___x_1583_ = lean_apply_3(v_f_1569_, v_b_1573_, v_key_1581_, v_val_1582_);
v___y_1575_ = v___x_1583_;
goto v___jp_1574_;
}
case 1:
{
lean_object* v_node_1584_; lean_object* v___x_1585_; 
v_node_1584_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_f_1569_);
v___x_1585_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1569_, v_node_1584_, v_b_1573_);
v___y_1575_ = v___x_1585_;
goto v___jp_1574_;
}
default: 
{
v___y_1575_ = v_b_1573_;
goto v___jp_1574_;
}
}
}
else
{
lean_dec(v_f_1569_);
return v_b_1573_;
}
v___jp_1574_:
{
size_t v___x_1576_; size_t v___x_1577_; 
v___x_1576_ = ((size_t)1ULL);
v___x_1577_ = lean_usize_add(v_i_1571_, v___x_1576_);
v_i_1571_ = v___x_1577_;
v_b_1573_ = v___y_1575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1586_, lean_object* v_as_1587_, lean_object* v_i_1588_, lean_object* v_stop_1589_, lean_object* v_b_1590_){
_start:
{
size_t v_i_boxed_1591_; size_t v_stop_boxed_1592_; lean_object* v_res_1593_; 
v_i_boxed_1591_ = lean_unbox_usize(v_i_1588_);
lean_dec(v_i_1588_);
v_stop_boxed_1592_ = lean_unbox_usize(v_stop_1589_);
lean_dec(v_stop_1589_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1586_, v_as_1587_, v_i_boxed_1591_, v_stop_boxed_1592_, v_b_1590_);
lean_dec_ref(v_as_1587_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(lean_object* v_f_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1594_, v_x_1595_, v_x_1596_);
lean_dec_ref(v_x_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object* v_d_1598_, lean_object* v_declName_1599_){
_start:
{
lean_object* v_tree_1600_; lean_object* v_erased_1601_; lean_object* v___f_1602_; lean_object* v___f_1603_; uint8_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v_tree_1600_ = lean_ctor_get(v_d_1598_, 0);
v_erased_1601_ = lean_ctor_get(v_d_1598_, 1);
lean_inc(v_declName_1599_);
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1602_, 0, v_declName_1599_);
v___f_1603_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1603_, 0, v___f_1602_);
v___x_1604_ = 0;
v___x_1605_ = lean_box(v___x_1604_);
v___x_1606_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v___f_1603_, v_tree_1600_, v___x_1605_);
v___x_1607_ = lean_unbox(v___x_1606_);
if (v___x_1607_ == 0)
{
uint8_t v___x_1608_; 
lean_dec(v_declName_1599_);
v___x_1608_ = lean_unbox(v___x_1606_);
lean_dec(v___x_1606_);
return v___x_1608_;
}
else
{
uint8_t v___x_1609_; uint8_t v___x_1610_; 
lean_dec(v___x_1606_);
v___x_1609_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_erased_1601_, v_declName_1599_);
lean_dec(v_declName_1599_);
v___x_1610_ = lean_bool_not(v___x_1609_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object* v_d_1611_, lean_object* v_declName_1612_){
_start:
{
uint8_t v_res_1613_; lean_object* v_r_1614_; 
v_res_1613_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1611_, v_declName_1612_);
lean_dec_ref(v_d_1611_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(lean_object* v_00_u03c3_1615_, lean_object* v_00_u03b1_1616_, lean_object* v_f_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1617_, v_x_1618_, v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(lean_object* v_00_u03c3_1621_, lean_object* v_00_u03b1_1622_, lean_object* v_f_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(v_00_u03c3_1621_, v_00_u03b1_1622_, v_f_1623_, v_x_1624_, v_x_1625_);
lean_dec_ref(v_x_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(lean_object* v_map_1627_, lean_object* v_f_1628_, lean_object* v_init_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1628_, v_map_1627_, v_init_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(lean_object* v_map_1631_, lean_object* v_f_1632_, lean_object* v_init_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(v_map_1631_, v_f_1632_, v_init_1633_);
lean_dec_ref(v_map_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(lean_object* v_00_u03c3_1635_, lean_object* v_00_u03b2_1636_, lean_object* v_map_1637_, lean_object* v_f_1638_, lean_object* v_init_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1638_, v_map_1637_, v_init_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(lean_object* v_00_u03c3_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_map_1643_, lean_object* v_f_1644_, lean_object* v_init_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(v_00_u03c3_1641_, v_00_u03b2_1642_, v_map_1643_, v_f_1644_, v_init_1645_);
lean_dec_ref(v_map_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
uint8_t v___x_1650_; 
v___x_1650_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1648_, v_x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(v_00_u03b2_1651_, v_x_1652_, v_x_1653_);
lean_dec(v_x_1653_);
lean_dec_ref(v_x_1652_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(lean_object* v_00_u03b1_1656_, lean_object* v_00_u03c3_1657_, lean_object* v_f_1658_, lean_object* v_as_1659_, size_t v_i_1660_, size_t v_stop_1661_, lean_object* v_b_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1658_, v_as_1659_, v_i_1660_, v_stop_1661_, v_b_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1664_, lean_object* v_00_u03c3_1665_, lean_object* v_f_1666_, lean_object* v_as_1667_, lean_object* v_i_1668_, lean_object* v_stop_1669_, lean_object* v_b_1670_){
_start:
{
size_t v_i_boxed_1671_; size_t v_stop_boxed_1672_; lean_object* v_res_1673_; 
v_i_boxed_1671_ = lean_unbox_usize(v_i_1668_);
lean_dec(v_i_1668_);
v_stop_boxed_1672_ = lean_unbox_usize(v_stop_1669_);
lean_dec(v_stop_1669_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_00_u03b1_1664_, v_00_u03c3_1665_, v_f_1666_, v_as_1667_, v_i_boxed_1671_, v_stop_boxed_1672_, v_b_1670_);
lean_dec_ref(v_as_1667_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(lean_object* v_00_u03b1_1674_, lean_object* v_00_u03c3_1675_, lean_object* v_f_1676_, lean_object* v_as_1677_, size_t v_i_1678_, size_t v_stop_1679_, lean_object* v_b_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1676_, v_as_1677_, v_i_1678_, v_stop_1679_, v_b_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_00_u03c3_1683_, lean_object* v_f_1684_, lean_object* v_as_1685_, lean_object* v_i_1686_, lean_object* v_stop_1687_, lean_object* v_b_1688_){
_start:
{
size_t v_i_boxed_1689_; size_t v_stop_boxed_1690_; lean_object* v_res_1691_; 
v_i_boxed_1689_ = lean_unbox_usize(v_i_1686_);
lean_dec(v_i_1686_);
v_stop_boxed_1690_ = lean_unbox_usize(v_stop_1687_);
lean_dec(v_stop_1687_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(v_00_u03b1_1682_, v_00_u03c3_1683_, v_f_1684_, v_as_1685_, v_i_boxed_1689_, v_stop_boxed_1690_, v_b_1688_);
lean_dec_ref(v_as_1685_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(lean_object* v_00_u03c3_1692_, lean_object* v_00_u03b1_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_f_1695_, lean_object* v_x_1696_, lean_object* v_x_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1695_, v_x_1696_, v_x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1699_, lean_object* v_00_u03b1_1700_, lean_object* v_00_u03b2_1701_, lean_object* v_f_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(v_00_u03c3_1699_, v_00_u03b1_1700_, v_00_u03b2_1701_, v_f_1702_, v_x_1703_, v_x_1704_);
lean_dec_ref(v_x_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(lean_object* v_00_u03b2_1706_, lean_object* v_x_1707_, size_t v_x_1708_, lean_object* v_x_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1707_, v_x_1708_, v_x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
size_t v_x_1500__boxed_1715_; uint8_t v_res_1716_; lean_object* v_r_1717_; 
v_x_1500__boxed_1715_ = lean_unbox_usize(v_x_1713_);
lean_dec(v_x_1713_);
v_res_1716_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(v_00_u03b2_1711_, v_x_1712_, v_x_1500__boxed_1715_, v_x_1714_);
lean_dec(v_x_1714_);
lean_dec_ref(v_x_1712_);
v_r_1717_ = lean_box(v_res_1716_);
return v_r_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_00_u03c3_1720_, lean_object* v_f_1721_, lean_object* v_as_1722_, size_t v_i_1723_, size_t v_stop_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1721_, v_as_1722_, v_i_1723_, v_stop_1724_, v_b_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_00_u03c3_1729_, lean_object* v_f_1730_, lean_object* v_as_1731_, lean_object* v_i_1732_, lean_object* v_stop_1733_, lean_object* v_b_1734_){
_start:
{
size_t v_i_boxed_1735_; size_t v_stop_boxed_1736_; lean_object* v_res_1737_; 
v_i_boxed_1735_ = lean_unbox_usize(v_i_1732_);
lean_dec(v_i_1732_);
v_stop_boxed_1736_ = lean_unbox_usize(v_stop_1733_);
lean_dec(v_stop_1733_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(v_00_u03b1_1727_, v_00_u03b2_1728_, v_00_u03c3_1729_, v_f_1730_, v_as_1731_, v_i_boxed_1735_, v_stop_boxed_1736_, v_b_1734_);
lean_dec_ref(v_as_1731_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1738_, lean_object* v_00_u03b1_1739_, lean_object* v_00_u03b2_1740_, lean_object* v_f_1741_, lean_object* v_keys_1742_, lean_object* v_vals_1743_, lean_object* v_heq_1744_, lean_object* v_i_1745_, lean_object* v_acc_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1741_, v_keys_1742_, v_vals_1743_, v_i_1745_, v_acc_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1748_, lean_object* v_00_u03b1_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_f_1751_, lean_object* v_keys_1752_, lean_object* v_vals_1753_, lean_object* v_heq_1754_, lean_object* v_i_1755_, lean_object* v_acc_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(v_00_u03c3_1748_, v_00_u03b1_1749_, v_00_u03b2_1750_, v_f_1751_, v_keys_1752_, v_vals_1753_, v_heq_1754_, v_i_1755_, v_acc_1756_);
lean_dec_ref(v_vals_1753_);
lean_dec_ref(v_keys_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1758_, lean_object* v_keys_1759_, lean_object* v_vals_1760_, lean_object* v_heq_1761_, lean_object* v_i_1762_, lean_object* v_k_1763_){
_start:
{
uint8_t v___x_1764_; 
v___x_1764_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1759_, v_i_1762_, v_k_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1765_, lean_object* v_keys_1766_, lean_object* v_vals_1767_, lean_object* v_heq_1768_, lean_object* v_i_1769_, lean_object* v_k_1770_){
_start:
{
uint8_t v_res_1771_; lean_object* v_r_1772_; 
v_res_1771_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(v_00_u03b2_1765_, v_keys_1766_, v_vals_1767_, v_heq_1768_, v_i_1769_, v_k_1770_);
lean_dec(v_k_1770_);
lean_dec_ref(v_vals_1767_);
lean_dec_ref(v_keys_1766_);
v_r_1772_ = lean_box(v_res_1771_);
return v_r_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg(lean_object* v_declName_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1776_; lean_object* v_env_1777_; lean_object* v___x_1778_; lean_object* v_ext_1779_; lean_object* v_toEnvExtension_1780_; lean_object* v_asyncMode_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1776_ = lean_st_ref_get(v_a_1774_);
v_env_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_ref(v_env_1777_);
lean_dec(v___x_1776_);
v___x_1778_ = l_Lean_Meta_Ext_extExtension;
v_ext_1779_ = lean_ctor_get(v___x_1778_, 1);
v_toEnvExtension_1780_ = lean_ctor_get(v_ext_1779_, 0);
v_asyncMode_1781_ = lean_ctor_get(v_toEnvExtension_1780_, 2);
v___x_1782_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1783_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1782_, v___x_1778_, v_env_1777_, v_asyncMode_1781_);
v___x_1784_ = l_Lean_Meta_Ext_ExtTheorems_contains(v___x_1783_, v_declName_1773_);
lean_dec(v___x_1783_);
v___x_1785_ = lean_box(v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg___boxed(lean_object* v_declName_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1787_, v_a_1788_);
lean_dec(v_a_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object* v_declName_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1791_, v_a_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object* v_declName_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_Ext_isExtTheorem(v_declName_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(lean_object* v_d_1801_, lean_object* v_declName_1802_, lean_object* v_toPure_1803_, lean_object* v_____r_1804_){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = l_Lean_Meta_Ext_ExtTheorems_eraseCore(v_d_1801_, v_declName_1802_);
v___x_1806_ = lean_apply_2(v_toPure_1803_, lean_box(0), v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1(lean_object* v___f_1807_, lean_object* v_____r_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_apply_1(v___f_1807_, v_____r_1808_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0));
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg(lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_d_1818_, lean_object* v_declName_1819_){
_start:
{
lean_object* v_toApplicative_1820_; lean_object* v_toBind_1821_; lean_object* v_toPure_1822_; lean_object* v___f_1823_; uint8_t v___x_1824_; 
v_toApplicative_1820_ = lean_ctor_get(v_inst_1816_, 0);
v_toBind_1821_ = lean_ctor_get(v_inst_1816_, 1);
lean_inc(v_toBind_1821_);
v_toPure_1822_ = lean_ctor_get(v_toApplicative_1820_, 1);
lean_inc(v_toPure_1822_);
lean_inc_n(v_declName_1819_, 2);
lean_inc_ref(v_d_1818_);
v___f_1823_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1823_, 0, v_d_1818_);
lean_closure_set(v___f_1823_, 1, v_declName_1819_);
lean_closure_set(v___f_1823_, 2, v_toPure_1822_);
v___x_1824_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1818_, v_declName_1819_);
if (v___x_1824_ == 0)
{
lean_object* v___f_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_d_1818_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1825_, 0, v___f_1823_);
v___x_1826_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1);
v___x_1827_ = l_Lean_MessageData_ofConstName(v_declName_1819_, v___x_1824_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = l_Lean_throwError___redArg(v_inst_1816_, v_inst_1817_, v___x_1830_);
v___x_1832_ = lean_apply_4(v_toBind_1821_, lean_box(0), lean_box(0), v___x_1831_, v___f_1825_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_inc(v_toPure_1822_);
lean_dec_ref(v___f_1823_);
lean_dec(v_toBind_1821_);
lean_dec_ref(v_inst_1817_);
lean_dec_ref(v_inst_1816_);
v___x_1833_ = lean_box(0);
v___x_1834_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(v_d_1818_, v_declName_1819_, v_toPure_1822_, v___x_1833_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object* v_m_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_d_1838_, lean_object* v_declName_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg(v_inst_1836_, v_inst_1837_, v_d_1838_, v_declName_1839_);
return v___x_1840_;
}
}
lean_object* runtime_initialize_Init_Data_Array_InsertionSort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Ext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_InsertionSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Ext_instInhabitedExtTheorems_default = _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default();
lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorems_default);
l_Lean_Meta_Ext_instInhabitedExtTheorems = _init_l_Lean_Meta_Ext_instInhabitedExtTheorems();
lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorems);
res = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Ext_extExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Ext_extExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Ext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_InsertionSort(uint8_t builtin);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Ext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_InsertionSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Ext(builtin);
}
#ifdef __cplusplus
}
#endif
