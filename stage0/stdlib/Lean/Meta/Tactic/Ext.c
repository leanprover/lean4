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
size_t v_x_1795__boxed_393_; lean_object* v_res_394_; 
v_x_1795__boxed_393_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_res_394_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_390_, v_x_1795__boxed_393_, v_x_392_);
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
size_t v_x_2024__boxed_547_; size_t v_x_2025__boxed_548_; lean_object* v_res_549_; 
v_x_2024__boxed_547_ = lean_unbox_usize(v_x_543_);
lean_dec(v_x_543_);
v_x_2025__boxed_548_ = lean_unbox_usize(v_x_544_);
lean_dec(v_x_544_);
v_res_549_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_x_542_, v_x_2024__boxed_547_, v_x_2025__boxed_548_, v_x_545_, v_x_546_);
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
uint8_t v___x_668_; 
v___x_668_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v___x_666_, v_k_662_);
if (v___x_668_ == 0)
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_lt(v___x_664_, v___x_663_);
if (v___x_669_ == 0)
{
lean_dec(v_k_660_);
lean_dec_ref(v_v_659_);
return v_as_661_;
}
else
{
lean_object* v___x_670_; lean_object* v_xs_x27_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_inc(v___x_666_);
v___x_670_ = lean_box(0);
v_xs_x27_671_ = lean_array_fset(v_as_661_, v___x_664_, v___x_670_);
v___x_672_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_666_);
v___x_673_ = lean_array_fset(v_xs_x27_671_, v___x_664_, v___x_672_);
return v___x_673_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_sub(v___x_663_, v___x_674_);
v___x_676_ = lean_array_fget_borrowed(v_as_661_, v___x_675_);
v___x_677_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v___x_676_, v_k_662_);
if (v___x_677_ == 0)
{
uint8_t v___x_678_; 
v___x_678_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_k_662_, v___x_676_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_lt(v___x_675_, v___x_663_);
if (v___x_679_ == 0)
{
lean_dec(v___x_675_);
lean_dec(v_k_660_);
lean_dec_ref(v_v_659_);
return v_as_661_;
}
else
{
lean_object* v___x_680_; lean_object* v_xs_x27_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_inc(v___x_676_);
v___x_680_ = lean_box(0);
v_xs_x27_681_ = lean_array_fset(v_as_661_, v___x_675_, v___x_680_);
v___x_682_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_676_);
v___x_683_ = lean_array_fset(v_xs_x27_681_, v___x_675_, v___x_682_);
lean_dec(v___x_675_);
return v___x_683_;
}
}
else
{
lean_object* v___x_684_; 
v___x_684_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v_as_661_, v_k_662_, v___x_664_, v___x_675_);
return v___x_684_;
}
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v___x_675_);
v___x_685_ = lean_box(0);
v___x_686_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_685_);
v___x_687_ = lean_array_push(v_as_661_, v___x_686_);
return v___x_687_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_as_690_; lean_object* v___x_691_; 
v___x_688_ = lean_box(0);
v___x_689_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_688_);
v_as_690_ = lean_array_push(v_as_661_, v___x_689_);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_664_, v_as_690_, v___x_663_);
return v___x_691_;
}
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_657_, v_keys_658_, v_v_659_, v_k_660_, v___x_692_);
v___x_694_ = lean_array_push(v_as_661_, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_keys_695_, lean_object* v_v_696_, lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
lean_object* v_vs_699_; lean_object* v_children_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_717_; 
v_vs_699_ = lean_ctor_get(v_x_698_, 0);
v_children_700_ = lean_ctor_get(v_x_698_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x_698_);
if (v_isSharedCheck_717_ == 0)
{
v___x_702_ = v_x_698_;
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_children_700_);
lean_inc(v_vs_699_);
lean_dec(v_x_698_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_717_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_array_get_size(v_keys_695_);
v___x_705_ = lean_nat_dec_lt(v_x_697_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_vs_699_, v_v_696_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_706_);
v___x_708_ = v___x_702_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_children_700_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v_k_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_c_713_; lean_object* v___x_715_; 
v_k_710_ = lean_array_fget_borrowed(v_keys_695_, v_x_697_);
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1));
lean_inc_n(v_k_710_, 2);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_k_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v_c_713_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_x_697_, v_keys_695_, v_v_696_, v_k_710_, v_children_700_, v___x_712_);
lean_dec_ref_known(v___x_712_, 2);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_c_713_);
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_vs_699_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_c_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(lean_object* v_x_718_, lean_object* v_keys_719_, lean_object* v_v_720_, lean_object* v_k_721_, lean_object* v_x_722_){
_start:
{
lean_object* v_snd_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_733_; 
v_snd_723_ = lean_ctor_get(v_x_722_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_x_722_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_x_722_, 0);
lean_dec(v_unused_734_);
v___x_725_ = v_x_722_;
v_isShared_726_ = v_isSharedCheck_733_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_snd_723_);
lean_dec(v_x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_733_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_c_729_; lean_object* v___x_731_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_x_718_, v___x_727_);
v_c_729_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_719_, v_v_720_, v___x_728_, v_snd_723_);
lean_dec(v___x_728_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v_c_729_);
lean_ctor_set(v___x_725_, 0, v_k_721_);
v___x_731_ = v___x_725_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_k_721_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_c_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_735_, lean_object* v_keys_736_, lean_object* v_v_737_, lean_object* v_k_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_735_, v_keys_736_, v_v_737_, v_k_738_, v_x_739_);
lean_dec_ref(v_keys_736_);
lean_dec(v_x_735_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_keys_741_, lean_object* v_v_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_741_, v_v_742_, v_x_743_, v_x_744_);
lean_dec(v_x_743_);
lean_dec_ref(v_keys_741_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_746_, lean_object* v_keys_747_, lean_object* v_v_748_, lean_object* v_k_749_, lean_object* v_as_750_, lean_object* v_k_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_746_, v_keys_747_, v_v_748_, v_k_749_, v_as_750_, v_k_751_, v_x_752_, v_x_753_);
lean_dec_ref(v_k_751_);
lean_dec_ref(v_keys_747_);
lean_dec(v_x_746_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_x_755_, lean_object* v_keys_756_, lean_object* v_v_757_, lean_object* v_k_758_, lean_object* v_as_759_, lean_object* v_k_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_x_755_, v_keys_756_, v_v_757_, v_k_758_, v_as_759_, v_k_760_);
lean_dec_ref(v_k_760_);
lean_dec_ref(v_keys_756_);
lean_dec(v_x_755_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v_keys_762_, lean_object* v_v_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_762_, v_v_763_, v___x_765_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
else
{
lean_object* v_val_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_777_; 
v_val_768_ = lean_ctor_get(v_x_764_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_764_);
if (v_isSharedCheck_777_ == 0)
{
v___x_770_ = v_x_764_;
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_val_768_);
lean_dec(v_x_764_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_777_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_762_, v_v_763_, v___x_772_, v_val_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v_keys_778_, lean_object* v_v_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_778_, v_v_779_, v_x_780_);
lean_dec_ref(v_keys_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_keys_782_, lean_object* v_v_783_, lean_object* v_x_784_, size_t v_x_785_, size_t v_x_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v_es_788_; size_t v___x_789_; size_t v___x_790_; lean_object* v_j_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_es_788_ = lean_ctor_get(v_x_784_, 0);
v___x_789_ = ((size_t)31ULL);
v___x_790_ = lean_usize_land(v_x_785_, v___x_789_);
v_j_791_ = lean_usize_to_nat(v___x_790_);
v___x_792_ = lean_array_get_size(v_es_788_);
v___x_793_ = lean_nat_dec_lt(v_j_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_j_791_);
lean_dec(v_x_787_);
lean_dec_ref(v_v_783_);
return v_x_784_;
}
else
{
lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_861_; 
lean_inc_ref(v_es_788_);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v_x_784_, 0);
lean_dec(v_unused_862_);
v___x_795_ = v_x_784_;
v_isShared_796_ = v_isSharedCheck_861_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_x_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_861_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_v_797_; lean_object* v___x_798_; lean_object* v_xs_x27_799_; lean_object* v___y_801_; 
v_v_797_ = lean_array_fget(v_es_788_, v_j_791_);
v___x_798_ = lean_box(0);
v_xs_x27_799_ = lean_array_fset(v_es_788_, v_j_791_, v___x_798_);
switch(lean_obj_tag(v_v_797_))
{
case 0:
{
lean_object* v_key_806_; lean_object* v_val_807_; uint8_t v___x_808_; 
v_key_806_ = lean_ctor_get(v_v_797_, 0);
v_val_807_ = lean_ctor_get(v_v_797_, 1);
v___x_808_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_787_, v_key_806_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_box(0);
v___x_810_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_782_, v_v_783_, v___x_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec(v_x_787_);
v___y_801_ = v_v_797_;
goto v___jp_800_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
lean_inc(v_val_807_);
lean_inc(v_key_806_);
lean_dec_ref_known(v_v_797_, 2);
v_val_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_819_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_806_, v_val_807_, v_x_787_, v_val_811_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_801_ = v___x_817_;
goto v___jp_800_;
}
}
}
}
else
{
lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_830_; 
lean_inc(v_val_807_);
v_isSharedCheck_830_ = !lean_is_exclusive(v_v_797_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; lean_object* v_unused_832_; 
v_unused_831_ = lean_ctor_get(v_v_797_, 1);
lean_dec(v_unused_831_);
v_unused_832_ = lean_ctor_get(v_v_797_, 0);
lean_dec(v_unused_832_);
v___x_821_ = v_v_797_;
v_isShared_822_ = v_isSharedCheck_830_;
goto v_resetjp_820_;
}
else
{
lean_dec(v_v_797_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_830_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_val_807_);
v___x_824_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_782_, v_v_783_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; 
lean_del_object(v___x_821_);
lean_dec(v_x_787_);
v___x_825_ = lean_box(2);
v___y_801_ = v___x_825_;
goto v___jp_800_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_828_; 
v_val_826_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_824_, 1);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v_val_826_);
lean_ctor_set(v___x_821_, 0, v_x_787_);
v___x_828_ = v___x_821_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_x_787_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_val_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v___y_801_ = v___x_828_;
goto v___jp_800_;
}
}
}
}
}
case 1:
{
lean_object* v_node_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_856_; 
v_node_833_ = lean_ctor_get(v_v_797_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_v_797_);
if (v_isSharedCheck_856_ == 0)
{
v___x_835_ = v_v_797_;
v_isShared_836_ = v_isSharedCheck_856_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_node_833_);
lean_dec(v_v_797_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_856_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v_newNode_841_; lean_object* v___x_842_; 
v___x_837_ = ((size_t)5ULL);
v___x_838_ = lean_usize_shift_right(v_x_785_, v___x_837_);
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_x_786_, v___x_839_);
v_newNode_841_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_782_, v_v_783_, v_node_833_, v___x_838_, v___x_840_, v_x_787_);
lean_inc_ref(v_newNode_841_);
v___x_842_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_844_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v_newNode_841_);
v___x_844_ = v___x_835_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_newNode_841_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
v___y_801_ = v___x_844_;
goto v___jp_800_;
}
}
else
{
lean_object* v_val_846_; lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_newNode_841_);
lean_del_object(v___x_835_);
v_val_846_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_842_, 1);
v_fst_847_ = lean_ctor_get(v_val_846_, 0);
v_snd_848_ = lean_ctor_get(v_val_846_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_val_846_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v_val_846_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_inc(v_fst_847_);
lean_dec(v_val_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_fst_847_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_snd_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v___y_801_ = v___x_853_;
goto v___jp_800_;
}
}
}
}
}
default: 
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_box(0);
v___x_858_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_782_, v_v_783_, v___x_857_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_dec(v_x_787_);
v___y_801_ = v_v_797_;
goto v___jp_800_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_860_; 
v_val_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_x_787_);
lean_ctor_set(v___x_860_, 1, v_val_859_);
v___y_801_ = v___x_860_;
goto v___jp_800_;
}
}
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_array_fset(v_xs_x27_799_, v_j_791_, v___y_801_);
lean_dec(v_j_791_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_802_);
v___x_804_ = v___x_795_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_object* v_ks_863_; lean_object* v_vs_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_897_; 
v_ks_863_ = lean_ctor_get(v_x_784_, 0);
v_vs_864_ = lean_ctor_get(v_x_784_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_897_ == 0)
{
v___x_866_ = v_x_784_;
v_isShared_867_ = v_isSharedCheck_897_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_vs_864_);
lean_inc(v_ks_863_);
lean_dec(v_x_784_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_897_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; 
v___x_868_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(v_ks_863_, v_x_787_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_870_; 
if (v_isShared_867_ == 0)
{
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_ks_863_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_vs_864_);
v___x_870_ = v_reuseFailAlloc_875_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_box(0);
v___x_872_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_782_, v_v_783_, v___x_871_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_dec(v_x_787_);
return v___x_870_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; 
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v___x_870_, v_x_785_, v_x_786_, v_x_787_, v_val_873_);
return v___x_874_;
}
}
}
else
{
lean_object* v_val_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_896_; 
v_val_876_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_896_ == 0)
{
v___x_878_ = v___x_868_;
v_isShared_879_ = v_isSharedCheck_896_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_val_876_);
lean_dec(v___x_868_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_896_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_v_x27_880_; lean_object* v_keys_881_; lean_object* v_vals_882_; lean_object* v___x_884_; 
v_v_x27_880_ = lean_array_fget(v_vs_864_, v_val_876_);
lean_inc(v_val_876_);
v_keys_881_ = l_Array_eraseIdx___redArg(v_ks_863_, v_val_876_);
v_vals_882_ = l_Array_eraseIdx___redArg(v_vs_864_, v_val_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_v_x27_880_);
v___x_884_ = v___x_878_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_v_x27_880_);
v___x_884_ = v_reuseFailAlloc_895_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_782_, v_v_783_, v___x_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_887_; 
lean_dec(v_x_787_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_vals_882_);
lean_ctor_set(v___x_866_, 0, v_keys_881_);
v___x_887_ = v___x_866_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_keys_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_vals_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v_val_889_; lean_object* v_keys_890_; lean_object* v_vals_891_; lean_object* v___x_893_; 
v_val_889_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___x_885_, 1);
v_keys_890_ = lean_array_push(v_keys_881_, v_x_787_);
v_vals_891_ = lean_array_push(v_vals_882_, v_val_889_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v_vals_891_);
lean_ctor_set(v___x_866_, 0, v_keys_890_);
v___x_893_ = v___x_866_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_keys_890_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_vals_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_keys_898_, lean_object* v_v_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
size_t v_x_2471__boxed_904_; size_t v_x_2472__boxed_905_; lean_object* v_res_906_; 
v_x_2471__boxed_904_ = lean_unbox_usize(v_x_901_);
lean_dec(v_x_901_);
v_x_2472__boxed_905_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_res_906_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_898_, v_v_899_, v_x_900_, v_x_2471__boxed_904_, v_x_2472__boxed_905_, v_x_903_);
lean_dec_ref(v_keys_898_);
return v_res_906_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_msg_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0);
v___x_910_ = lean_panic_fn_borrowed(v___x_909_, v_msg_908_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_914_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2));
v___x_915_ = lean_unsigned_to_nat(23u);
v___x_916_ = lean_unsigned_to_nat(166u);
v___x_917_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1));
v___x_918_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0));
v___x_919_ = l_mkPanicMessageWithDecl(v___x_918_, v___x_917_, v___x_916_, v___x_915_, v___x_914_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(lean_object* v_d_920_, lean_object* v_keys_921_, lean_object* v_v_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = lean_array_get_size(v_keys_921_);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_nat_dec_eq(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v_k_927_; uint64_t v___x_928_; size_t v_h_929_; size_t v___x_930_; lean_object* v___x_931_; 
v___x_926_ = lean_box(0);
v_k_927_ = lean_array_get_borrowed(v___x_926_, v_keys_921_, v___x_924_);
v___x_928_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_927_);
v_h_929_ = lean_uint64_to_usize(v___x_928_);
v___x_930_ = ((size_t)1ULL);
lean_inc(v_k_927_);
v___x_931_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_921_, v_v_922_, v_d_920_, v_h_929_, v___x_930_, v_k_927_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v_v_922_);
lean_dec_ref(v_d_920_);
v___x_932_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3);
v___x_933_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_934_, lean_object* v_keys_935_, lean_object* v_v_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_d_934_, v_keys_935_, v_v_936_);
lean_dec_ref(v_keys_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_938_, lean_object* v_thm_939_){
_start:
{
lean_object* v_tree_940_; lean_object* v_erased_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_952_; 
v_tree_940_ = lean_ctor_get(v_x_938_, 0);
v_erased_941_ = lean_ctor_get(v_x_938_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_952_ == 0)
{
v___x_943_ = v_x_938_;
v_isShared_944_ = v_isSharedCheck_952_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_erased_941_);
lean_inc(v_tree_940_);
lean_dec(v_x_938_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_952_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_declName_945_; lean_object* v_keys_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
v_declName_945_ = lean_ctor_get(v_thm_939_, 0);
lean_inc(v_declName_945_);
v_keys_946_ = lean_ctor_get(v_thm_939_, 2);
lean_inc_ref(v_keys_946_);
v___x_947_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_tree_940_, v_keys_946_, v_thm_939_);
lean_dec_ref(v_keys_946_);
v___x_948_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_erased_941_, v_declName_945_);
lean_dec(v_declName_945_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_948_);
lean_ctor_set(v___x_943_, 0, v___x_947_);
v___x_950_ = v___x_943_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v___y_953_){
_start:
{
lean_inc_ref(v___y_953_);
return v___y_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v___y_954_);
lean_dec_ref(v___y_954_);
return v_res_955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___f_968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___f_969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_970_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3);
v___f_971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___f_971_);
lean_ctor_set(v___x_973_, 2, v___x_970_);
lean_ctor_set(v___x_973_, 3, v___f_969_);
lean_ctor_set(v___x_973_, 4, v___f_968_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_);
v___x_976_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_980_, v_x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(v_00_u03b2_983_, v_x_984_, v_x_985_);
lean_dec(v_x_985_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, size_t v_x_989_, lean_object* v_x_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_988_, v_x_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
size_t v_x_2840__boxed_996_; lean_object* v_res_997_; 
v_x_2840__boxed_996_ = lean_unbox_usize(v_x_994_);
lean_dec(v_x_994_);
v_res_997_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_992_, v_x_993_, v_x_2840__boxed_996_, v_x_995_);
lean_dec(v_x_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(lean_object* v_00_u03b2_998_, lean_object* v_x_999_, size_t v_x_1000_, size_t v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_x_999_, v_x_1000_, v_x_1001_, v_x_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
size_t v_x_2851__boxed_1011_; size_t v_x_2852__boxed_1012_; lean_object* v_res_1013_; 
v_x_2851__boxed_1011_ = lean_unbox_usize(v_x_1007_);
lean_dec(v_x_1007_);
v_x_2852__boxed_1012_ = lean_unbox_usize(v_x_1008_);
lean_dec(v_x_1008_);
v_res_1013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(v_00_u03b2_1005_, v_x_1006_, v_x_2851__boxed_1011_, v_x_2852__boxed_1012_, v_x_1009_, v_x_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_x_1014_, lean_object* v_keys_1015_, lean_object* v_v_1016_, lean_object* v_k_1017_, lean_object* v_as_1018_, lean_object* v_k_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_1014_, v_keys_1015_, v_v_1016_, v_k_1017_, v_as_1018_, v_k_1019_, v_x_1020_, v_x_1021_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_x_1025_, lean_object* v_keys_1026_, lean_object* v_v_1027_, lean_object* v_k_1028_, lean_object* v_as_1029_, lean_object* v_k_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_x_1025_, v_keys_1026_, v_v_1027_, v_k_1028_, v_as_1029_, v_k_1030_, v_x_1031_, v_x_1032_, v_x_1033_, v_x_1034_);
lean_dec_ref(v_k_1030_);
lean_dec_ref(v_keys_1026_);
lean_dec(v_x_1025_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1036_, lean_object* v_n_1037_, lean_object* v_k_1038_, lean_object* v_v_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(v_n_1037_, v_k_1038_, v_v_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_1041_, size_t v_depth_1042_, lean_object* v_keys_1043_, lean_object* v_vals_1044_, lean_object* v_heq_1045_, lean_object* v_i_1046_, lean_object* v_entries_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(v_depth_1042_, v_keys_1043_, v_vals_1044_, v_i_1046_, v_entries_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_depth_1050_, lean_object* v_keys_1051_, lean_object* v_vals_1052_, lean_object* v_heq_1053_, lean_object* v_i_1054_, lean_object* v_entries_1055_){
_start:
{
size_t v_depth_boxed_1056_; lean_object* v_res_1057_; 
v_depth_boxed_1056_ = lean_unbox_usize(v_depth_1050_);
lean_dec(v_depth_1050_);
v_res_1057_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12(v_00_u03b2_1049_, v_depth_boxed_1056_, v_keys_1051_, v_vals_1052_, v_heq_1053_, v_i_1054_, v_entries_1055_);
lean_dec_ref(v_vals_1052_);
lean_dec_ref(v_keys_1051_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(v_x_1059_, v_x_1060_, v_x_1061_, v_x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_getExtTheorems___lam__0(lean_object* v_x1_1064_, lean_object* v_x2_1065_){
_start:
{
lean_object* v_priority_1066_; lean_object* v_priority_1067_; uint8_t v___x_1068_; 
v_priority_1066_ = lean_ctor_get(v_x1_1064_, 1);
v_priority_1067_ = lean_ctor_get(v_x2_1065_, 1);
v___x_1068_ = lean_nat_dec_lt(v_priority_1066_, v_priority_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(lean_object* v_x1_1069_, lean_object* v_x2_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_Meta_Ext_getExtTheorems___lam__0(v_x1_1069_, v_x2_1070_);
lean_dec_ref(v_x2_1070_);
lean_dec_ref(v_x1_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__1(lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v_x1_1076_, lean_object* v_x2_1077_){
_start:
{
lean_object* v_erased_1078_; lean_object* v_declName_1079_; uint8_t v___x_1080_; 
v_erased_1078_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_erased_1078_);
lean_dec_ref(v___x_1073_);
v_declName_1079_ = lean_ctor_get(v_x2_1077_, 0);
lean_inc(v_declName_1079_);
v___x_1080_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1074_, v___x_1075_, v_erased_1078_, v_declName_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_array_push(v_x1_1076_, v_x2_1077_);
return v___x_1081_;
}
else
{
lean_dec_ref(v_x2_1077_);
return v_x1_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object* v_ty_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v_env_1111_; lean_object* v___x_1112_; lean_object* v_ext_1113_; lean_object* v_toEnvExtension_1114_; lean_object* v_asyncMode_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_tree_1118_; lean_object* v___x_1119_; 
v___x_1110_ = lean_st_ref_get(v_a_1108_);
v_env_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_env_1111_);
lean_dec(v___x_1110_);
v___x_1112_ = l_Lean_Meta_Ext_extExtension;
v_ext_1113_ = lean_ctor_get(v___x_1112_, 1);
v_toEnvExtension_1114_ = lean_ctor_get(v_ext_1113_, 0);
v_asyncMode_1115_ = lean_ctor_get(v_toEnvExtension_1114_, 2);
v___x_1116_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1117_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1116_, v___x_1112_, v_env_1111_, v_asyncMode_1115_);
v_tree_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc_ref(v_tree_1118_);
v___x_1119_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_tree_1118_, v_ty_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec_ref(v_tree_1118_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1149_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1149_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1149_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___f_1124_; lean_object* v___y_1126_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___f_1124_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__0));
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_array_get_size(v_a_1120_);
v___x_1136_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_1137_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__10));
v___x_1138_ = lean_nat_dec_lt(v___x_1134_, v___x_1135_);
if (v___x_1138_ == 0)
{
lean_dec(v_a_1120_);
lean_dec(v___x_1117_);
v___y_1126_ = v___x_1136_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___f_1141_; uint8_t v___x_1142_; 
v___x_1139_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__11));
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__12));
v___f_1141_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_getExtTheorems___lam__1), 5, 3);
lean_closure_set(v___f_1141_, 0, v___x_1117_);
lean_closure_set(v___f_1141_, 1, v___x_1139_);
lean_closure_set(v___f_1141_, 2, v___x_1140_);
v___x_1142_ = lean_nat_dec_le(v___x_1135_, v___x_1135_);
if (v___x_1142_ == 0)
{
if (v___x_1138_ == 0)
{
lean_dec_ref(v___f_1141_);
lean_dec(v_a_1120_);
v___y_1126_ = v___x_1136_;
goto v___jp_1125_;
}
else
{
size_t v___x_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = lean_usize_of_nat(v___x_1135_);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1137_, v___f_1141_, v_a_1120_, v___x_1143_, v___x_1144_, v___x_1136_);
v___y_1126_ = v___x_1145_;
goto v___jp_1125_;
}
}
else
{
size_t v___x_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = lean_usize_of_nat(v___x_1135_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1137_, v___f_1141_, v_a_1120_, v___x_1146_, v___x_1147_, v___x_1136_);
v___y_1126_ = v___x_1148_;
goto v___jp_1125_;
}
}
v___jp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_array_get_size(v___y_1126_);
v___x_1129_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(lean_box(0), v___f_1124_, v___y_1126_, v___x_1127_, v___x_1128_);
v___x_1130_ = l_Array_reverse___redArg(v___x_1129_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1130_);
v___x_1132_ = v___x_1122_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_dec(v___x_1117_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___boxed(lean_object* v_ty_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Meta_Ext_getExtTheorems(v_ty_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v_ks_1161_; lean_object* v_vs_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1186_; 
v_ks_1161_ = lean_ctor_get(v_x_1157_, 0);
v_vs_1162_ = lean_ctor_get(v_x_1157_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x_1157_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1164_ = v_x_1157_;
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_vs_1162_);
lean_inc(v_ks_1161_);
lean_dec(v_x_1157_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_array_get_size(v_ks_1161_);
v___x_1167_ = lean_nat_dec_lt(v_x_1158_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_dec(v_x_1158_);
v___x_1168_ = lean_array_push(v_ks_1161_, v_x_1159_);
v___x_1169_ = lean_array_push(v_vs_1162_, v_x_1160_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1169_);
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1171_ = v___x_1164_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
lean_object* v_k_x27_1173_; uint8_t v___x_1174_; 
v_k_x27_1173_ = lean_array_fget_borrowed(v_ks_1161_, v_x_1158_);
v___x_1174_ = lean_name_eq(v_x_1159_, v_k_x27_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1176_; 
if (v_isShared_1165_ == 0)
{
v___x_1176_ = v___x_1164_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_ks_1161_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_vs_1162_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_nat_add(v_x_1158_, v___x_1177_);
lean_dec(v_x_1158_);
v_x_1157_ = v___x_1176_;
v_x_1158_ = v___x_1178_;
goto _start;
}
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1181_ = lean_array_fset(v_ks_1161_, v_x_1158_, v_x_1159_);
v___x_1182_ = lean_array_fset(v_vs_1162_, v_x_1158_, v_x_1160_);
lean_dec(v_x_1158_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1182_);
lean_ctor_set(v___x_1164_, 0, v___x_1181_);
v___x_1184_ = v___x_1164_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1187_, lean_object* v_k_1188_, lean_object* v_v_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1187_, v___x_1190_, v_k_1188_, v_v_1189_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(lean_object* v_x_1193_, size_t v_x_1194_, size_t v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
lean_object* v_es_1198_; size_t v___x_1199_; size_t v___x_1200_; lean_object* v_j_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_es_1198_ = lean_ctor_get(v_x_1193_, 0);
v___x_1199_ = ((size_t)31ULL);
v___x_1200_ = lean_usize_land(v_x_1194_, v___x_1199_);
v_j_1201_ = lean_usize_to_nat(v___x_1200_);
v___x_1202_ = lean_array_get_size(v_es_1198_);
v___x_1203_ = lean_nat_dec_lt(v_j_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_dec(v_j_1201_);
lean_dec(v_x_1197_);
lean_dec(v_x_1196_);
return v_x_1193_;
}
else
{
lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1242_; 
lean_inc_ref(v_es_1198_);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1193_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_x_1193_, 0);
lean_dec(v_unused_1243_);
v___x_1205_ = v_x_1193_;
v_isShared_1206_ = v_isSharedCheck_1242_;
goto v_resetjp_1204_;
}
else
{
lean_dec(v_x_1193_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1242_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v_v_1207_; lean_object* v___x_1208_; lean_object* v_xs_x27_1209_; lean_object* v___y_1211_; 
v_v_1207_ = lean_array_fget(v_es_1198_, v_j_1201_);
v___x_1208_ = lean_box(0);
v_xs_x27_1209_ = lean_array_fset(v_es_1198_, v_j_1201_, v___x_1208_);
switch(lean_obj_tag(v_v_1207_))
{
case 0:
{
lean_object* v_key_1216_; lean_object* v_val_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1227_; 
v_key_1216_ = lean_ctor_get(v_v_1207_, 0);
v_val_1217_ = lean_ctor_get(v_v_1207_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_v_1207_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1219_ = v_v_1207_;
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_val_1217_);
lean_inc(v_key_1216_);
lean_dec(v_v_1207_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_name_eq(v_x_1196_, v_key_1216_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_del_object(v___x_1219_);
v___x_1222_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1216_, v_val_1217_, v_x_1196_, v_x_1197_);
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
v___y_1211_ = v___x_1223_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1225_; 
lean_dec(v_val_1217_);
lean_dec(v_key_1216_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v_x_1197_);
lean_ctor_set(v___x_1219_, 0, v_x_1196_);
v___x_1225_ = v___x_1219_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_x_1196_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_x_1197_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v___y_1211_ = v___x_1225_;
goto v___jp_1210_;
}
}
}
}
case 1:
{
lean_object* v_node_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1240_; 
v_node_1228_ = lean_ctor_get(v_v_1207_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_v_1207_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1230_ = v_v_1207_;
v_isShared_1231_ = v_isSharedCheck_1240_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_node_1228_);
lean_dec(v_v_1207_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1240_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1232_ = ((size_t)5ULL);
v___x_1233_ = lean_usize_shift_right(v_x_1194_, v___x_1232_);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_add(v_x_1195_, v___x_1234_);
v___x_1236_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_node_1228_, v___x_1233_, v___x_1235_, v_x_1196_, v_x_1197_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1236_);
v___x_1238_ = v___x_1230_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
v___y_1211_ = v___x_1238_;
goto v___jp_1210_;
}
}
}
default: 
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_x_1196_);
lean_ctor_set(v___x_1241_, 1, v_x_1197_);
v___y_1211_ = v___x_1241_;
goto v___jp_1210_;
}
}
v___jp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_array_fset(v_xs_x27_1209_, v_j_1201_, v___y_1211_);
lean_dec(v_j_1201_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1212_);
v___x_1214_ = v___x_1205_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
else
{
lean_object* v_ks_1244_; lean_object* v_vs_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1265_; 
v_ks_1244_ = lean_ctor_get(v_x_1193_, 0);
v_vs_1245_ = lean_ctor_get(v_x_1193_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_x_1193_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1247_ = v_x_1193_;
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_vs_1245_);
lean_inc(v_ks_1244_);
lean_dec(v_x_1193_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1265_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_ks_1244_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_vs_1245_);
v___x_1250_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v_newNode_1251_; uint8_t v___y_1253_; size_t v___x_1259_; uint8_t v___x_1260_; 
v_newNode_1251_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v___x_1250_, v_x_1196_, v_x_1197_);
v___x_1259_ = ((size_t)7ULL);
v___x_1260_ = lean_usize_dec_le(v___x_1259_, v_x_1195_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1251_);
v___x_1262_ = lean_unsigned_to_nat(4u);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
lean_dec(v___x_1261_);
v___y_1253_ = v___x_1263_;
goto v___jp_1252_;
}
else
{
v___y_1253_ = v___x_1260_;
goto v___jp_1252_;
}
v___jp_1252_:
{
if (v___y_1253_ == 0)
{
lean_object* v_ks_1254_; lean_object* v_vs_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_ks_1254_ = lean_ctor_get(v_newNode_1251_, 0);
lean_inc_ref(v_ks_1254_);
v_vs_1255_ = lean_ctor_get(v_newNode_1251_, 1);
lean_inc_ref(v_vs_1255_);
lean_dec_ref(v_newNode_1251_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0);
v___x_1258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_x_1195_, v_ks_1254_, v_vs_1255_, v___x_1256_, v___x_1257_);
lean_dec_ref(v_vs_1255_);
lean_dec_ref(v_ks_1254_);
return v___x_1258_;
}
else
{
return v_newNode_1251_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_1266_, lean_object* v_keys_1267_, lean_object* v_vals_1268_, lean_object* v_i_1269_, lean_object* v_entries_1270_){
_start:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = lean_array_get_size(v_keys_1267_);
v___x_1272_ = lean_nat_dec_lt(v_i_1269_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v_i_1269_);
return v_entries_1270_;
}
else
{
lean_object* v_k_1273_; lean_object* v_v_1274_; uint64_t v___y_1276_; 
v_k_1273_ = lean_array_fget_borrowed(v_keys_1267_, v_i_1269_);
v_v_1274_ = lean_array_fget_borrowed(v_vals_1268_, v_i_1269_);
if (lean_obj_tag(v_k_1273_) == 0)
{
uint64_t v___x_1287_; 
v___x_1287_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1276_ = v___x_1287_;
goto v___jp_1275_;
}
else
{
uint64_t v_hash_1288_; 
v_hash_1288_ = lean_ctor_get_uint64(v_k_1273_, sizeof(void*)*2);
v___y_1276_ = v_hash_1288_;
goto v___jp_1275_;
}
v___jp_1275_:
{
size_t v_h_1277_; size_t v___x_1278_; lean_object* v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; size_t v___x_1282_; size_t v_h_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_h_1277_ = lean_uint64_to_usize(v___y_1276_);
v___x_1278_ = ((size_t)5ULL);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_sub(v_depth_1266_, v___x_1280_);
v___x_1282_ = lean_usize_mul(v___x_1278_, v___x_1281_);
v_h_1283_ = lean_usize_shift_right(v_h_1277_, v___x_1282_);
v___x_1284_ = lean_nat_add(v_i_1269_, v___x_1279_);
lean_dec(v_i_1269_);
lean_inc(v_v_1274_);
lean_inc(v_k_1273_);
v___x_1285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_entries_1270_, v_h_1283_, v_depth_1266_, v_k_1273_, v_v_1274_);
v_i_1269_ = v___x_1284_;
v_entries_1270_ = v___x_1285_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1289_, lean_object* v_keys_1290_, lean_object* v_vals_1291_, lean_object* v_i_1292_, lean_object* v_entries_1293_){
_start:
{
size_t v_depth_boxed_1294_; lean_object* v_res_1295_; 
v_depth_boxed_1294_ = lean_unbox_usize(v_depth_1289_);
lean_dec(v_depth_1289_);
v_res_1295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1294_, v_keys_1290_, v_vals_1291_, v_i_1292_, v_entries_1293_);
lean_dec_ref(v_vals_1291_);
lean_dec_ref(v_keys_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
size_t v_x_363__boxed_1301_; size_t v_x_364__boxed_1302_; lean_object* v_res_1303_; 
v_x_363__boxed_1301_ = lean_unbox_usize(v_x_1297_);
lean_dec(v_x_1297_);
v_x_364__boxed_1302_ = lean_unbox_usize(v_x_1298_);
lean_dec(v_x_1298_);
v_res_1303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1296_, v_x_363__boxed_1301_, v_x_364__boxed_1302_, v_x_1299_, v_x_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(lean_object* v_x_1304_, lean_object* v_x_1305_, lean_object* v_x_1306_){
_start:
{
uint64_t v___y_1308_; 
if (lean_obj_tag(v_x_1305_) == 0)
{
uint64_t v___x_1312_; 
v___x_1312_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1308_ = v___x_1312_;
goto v___jp_1307_;
}
else
{
uint64_t v_hash_1313_; 
v_hash_1313_ = lean_ctor_get_uint64(v_x_1305_, sizeof(void*)*2);
v___y_1308_ = v_hash_1313_;
goto v___jp_1307_;
}
v___jp_1307_:
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_uint64_to_usize(v___y_1308_);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1304_, v___x_1309_, v___x_1310_, v_x_1305_, v_x_1306_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object* v_d_1314_, lean_object* v_declName_1315_){
_start:
{
lean_object* v_tree_1316_; lean_object* v_erased_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1326_; 
v_tree_1316_ = lean_ctor_get(v_d_1314_, 0);
v_erased_1317_ = lean_ctor_get(v_d_1314_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_d_1314_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1319_ = v_d_1314_;
v_isShared_1320_ = v_isSharedCheck_1326_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_erased_1317_);
lean_inc(v_tree_1316_);
lean_dec(v_d_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1326_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_erased_1317_, v_declName_1315_, v___x_1321_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v___x_1322_);
v___x_1324_ = v___x_1319_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_tree_1316_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0(lean_object* v_00_u03b2_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_, lean_object* v_x_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_x_1328_, v_x_1329_, v_x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(lean_object* v_00_u03b2_1332_, lean_object* v_x_1333_, size_t v_x_1334_, size_t v_x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1333_, v_x_1334_, v_x_1335_, v_x_1336_, v_x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
size_t v_x_568__boxed_1345_; size_t v_x_569__boxed_1346_; lean_object* v_res_1347_; 
v_x_568__boxed_1345_ = lean_unbox_usize(v_x_1341_);
lean_dec(v_x_1341_);
v_x_569__boxed_1346_ = lean_unbox_usize(v_x_1342_);
lean_dec(v_x_1342_);
v_res_1347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(v_00_u03b2_1339_, v_x_1340_, v_x_568__boxed_1345_, v_x_569__boxed_1346_, v_x_1343_, v_x_1344_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1348_, lean_object* v_n_1349_, lean_object* v_k_1350_, lean_object* v_v_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v_n_1349_, v_k_1350_, v_v_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1353_, size_t v_depth_1354_, lean_object* v_keys_1355_, lean_object* v_vals_1356_, lean_object* v_heq_1357_, lean_object* v_i_1358_, lean_object* v_entries_1359_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_1354_, v_keys_1355_, v_vals_1356_, v_i_1358_, v_entries_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1361_, lean_object* v_depth_1362_, lean_object* v_keys_1363_, lean_object* v_vals_1364_, lean_object* v_heq_1365_, lean_object* v_i_1366_, lean_object* v_entries_1367_){
_start:
{
size_t v_depth_boxed_1368_; lean_object* v_res_1369_; 
v_depth_boxed_1368_ = lean_unbox_usize(v_depth_1362_);
lean_dec(v_depth_1362_);
v_res_1369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(v_00_u03b2_1361_, v_depth_boxed_1368_, v_keys_1363_, v_vals_1364_, v_heq_1365_, v_i_1366_, v_entries_1367_);
lean_dec_ref(v_vals_1364_);
lean_dec_ref(v_keys_1363_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1371_, v_x_1372_, v_x_1373_, v_x_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(lean_object* v_declName_1376_, uint8_t v_x1_1377_, lean_object* v_x2_1378_){
_start:
{
if (v_x1_1377_ == 0)
{
lean_object* v_declName_1379_; uint8_t v___x_1380_; 
v_declName_1379_ = lean_ctor_get(v_x2_1378_, 0);
v___x_1380_ = lean_name_eq(v_declName_1379_, v_declName_1376_);
return v___x_1380_;
}
else
{
return v_x1_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(lean_object* v_declName_1381_, lean_object* v_x1_1382_, lean_object* v_x2_1383_){
_start:
{
uint8_t v_x1_1195__boxed_1384_; uint8_t v_res_1385_; lean_object* v_r_1386_; 
v_x1_1195__boxed_1384_ = lean_unbox(v_x1_1382_);
v_res_1385_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(v_declName_1381_, v_x1_1195__boxed_1384_, v_x2_1383_);
lean_dec_ref(v_x2_1383_);
lean_dec(v_declName_1381_);
v_r_1386_ = lean_box(v_res_1385_);
return v_r_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(lean_object* v_f_1387_, lean_object* v_as_1388_, size_t v_i_1389_, size_t v_stop_1390_, lean_object* v_b_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_usize_dec_eq(v_i_1389_, v_stop_1390_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; size_t v___x_1395_; size_t v___x_1396_; 
v___x_1393_ = lean_array_uget_borrowed(v_as_1388_, v_i_1389_);
lean_inc(v_f_1387_);
lean_inc(v___x_1393_);
v___x_1394_ = lean_apply_2(v_f_1387_, v_b_1391_, v___x_1393_);
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1389_, v___x_1395_);
v_i_1389_ = v___x_1396_;
v_b_1391_ = v___x_1394_;
goto _start;
}
else
{
lean_dec(v_f_1387_);
return v_b_1391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg___boxed(lean_object* v_f_1398_, lean_object* v_as_1399_, lean_object* v_i_1400_, lean_object* v_stop_1401_, lean_object* v_b_1402_){
_start:
{
size_t v_i_boxed_1403_; size_t v_stop_boxed_1404_; lean_object* v_res_1405_; 
v_i_boxed_1403_ = lean_unbox_usize(v_i_1400_);
lean_dec(v_i_1400_);
v_stop_boxed_1404_ = lean_unbox_usize(v_stop_1401_);
lean_dec(v_stop_1401_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1398_, v_as_1399_, v_i_boxed_1403_, v_stop_boxed_1404_, v_b_1402_);
lean_dec_ref(v_as_1399_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(lean_object* v_f_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
lean_object* v_vs_1409_; lean_object* v_children_1410_; lean_object* v___x_1411_; lean_object* v_s_1413_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_vs_1409_ = lean_ctor_get(v_x_1408_, 0);
v_children_1410_ = lean_ctor_get(v_x_1408_, 1);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1423_ = lean_array_get_size(v_vs_1409_);
v___x_1424_ = lean_nat_dec_lt(v___x_1411_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = lean_array_get_size(v_children_1410_);
v___x_1426_ = lean_nat_dec_lt(v___x_1411_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_dec(v_f_1406_);
return v_x_1407_;
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_nat_dec_le(v___x_1425_, v___x_1425_);
if (v___x_1427_ == 0)
{
if (v___x_1426_ == 0)
{
lean_dec(v_f_1406_);
return v_x_1407_;
}
else
{
size_t v___x_1428_; size_t v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = lean_usize_of_nat(v___x_1425_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1406_, v_children_1410_, v___x_1428_, v___x_1429_, v_x_1407_);
return v___x_1430_;
}
}
else
{
size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = ((size_t)0ULL);
v___x_1432_ = lean_usize_of_nat(v___x_1425_);
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1406_, v_children_1410_, v___x_1431_, v___x_1432_, v_x_1407_);
return v___x_1433_;
}
}
}
else
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_nat_dec_le(v___x_1423_, v___x_1423_);
if (v___x_1434_ == 0)
{
if (v___x_1424_ == 0)
{
v_s_1413_ = v_x_1407_;
goto v___jp_1412_;
}
else
{
size_t v___x_1435_; size_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = lean_usize_of_nat(v___x_1423_);
lean_inc(v_f_1406_);
v___x_1437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1406_, v_vs_1409_, v___x_1435_, v___x_1436_, v_x_1407_);
v_s_1413_ = v___x_1437_;
goto v___jp_1412_;
}
}
else
{
size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = ((size_t)0ULL);
v___x_1439_ = lean_usize_of_nat(v___x_1423_);
lean_inc(v_f_1406_);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1406_, v_vs_1409_, v___x_1438_, v___x_1439_, v_x_1407_);
v_s_1413_ = v___x_1440_;
goto v___jp_1412_;
}
}
v___jp_1412_:
{
lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1414_ = lean_array_get_size(v_children_1410_);
v___x_1415_ = lean_nat_dec_lt(v___x_1411_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_dec(v_f_1406_);
return v_s_1413_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_le(v___x_1414_, v___x_1414_);
if (v___x_1416_ == 0)
{
if (v___x_1415_ == 0)
{
lean_dec(v_f_1406_);
return v_s_1413_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1414_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1406_, v_children_1410_, v___x_1417_, v___x_1418_, v_s_1413_);
return v___x_1419_;
}
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1414_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1406_, v_children_1410_, v___x_1420_, v___x_1421_, v_s_1413_);
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(lean_object* v_f_1441_, lean_object* v_as_1442_, size_t v_i_1443_, size_t v_stop_1444_, lean_object* v_b_1445_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_usize_dec_eq(v_i_1443_, v_stop_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v_snd_1448_; lean_object* v___x_1449_; size_t v___x_1450_; size_t v___x_1451_; 
v___x_1447_ = lean_array_uget_borrowed(v_as_1442_, v_i_1443_);
v_snd_1448_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_f_1441_);
v___x_1449_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1441_, v_b_1445_, v_snd_1448_);
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_add(v_i_1443_, v___x_1450_);
v_i_1443_ = v___x_1451_;
v_b_1445_ = v___x_1449_;
goto _start;
}
else
{
lean_dec(v_f_1441_);
return v_b_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_f_1453_, lean_object* v_as_1454_, lean_object* v_i_1455_, lean_object* v_stop_1456_, lean_object* v_b_1457_){
_start:
{
size_t v_i_boxed_1458_; size_t v_stop_boxed_1459_; lean_object* v_res_1460_; 
v_i_boxed_1458_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_stop_boxed_1459_ = lean_unbox_usize(v_stop_1456_);
lean_dec(v_stop_1456_);
v_res_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1453_, v_as_1454_, v_i_boxed_1458_, v_stop_boxed_1459_, v_b_1457_);
lean_dec_ref(v_as_1454_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg___boxed(lean_object* v_f_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1461_, v_x_1462_, v_x_1463_);
lean_dec_ref(v_x_1463_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(lean_object* v___f_1465_, uint8_t v_s_1466_, lean_object* v_x_1467_, lean_object* v_t_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_box(v_s_1466_);
v___x_1470_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v___f_1465_, v___x_1469_, v_t_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed(lean_object* v___f_1471_, lean_object* v_s_1472_, lean_object* v_x_1473_, lean_object* v_t_1474_){
_start:
{
uint8_t v_s_boxed_1475_; lean_object* v_res_1476_; 
v_s_boxed_1475_ = lean_unbox(v_s_1472_);
v_res_1476_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(v___f_1471_, v_s_boxed_1475_, v_x_1473_, v_t_1474_);
lean_dec_ref(v_t_1474_);
lean_dec(v_x_1473_);
return v_res_1476_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(lean_object* v_keys_1477_, lean_object* v_i_1478_, lean_object* v_k_1479_){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_array_get_size(v_keys_1477_);
v___x_1481_ = lean_nat_dec_lt(v_i_1478_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_dec(v_i_1478_);
return v___x_1481_;
}
else
{
lean_object* v_k_x27_1482_; uint8_t v___x_1483_; 
v_k_x27_1482_ = lean_array_fget_borrowed(v_keys_1477_, v_i_1478_);
v___x_1483_ = lean_name_eq(v_k_1479_, v_k_x27_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_add(v_i_1478_, v___x_1484_);
lean_dec(v_i_1478_);
v_i_1478_ = v___x_1485_;
goto _start;
}
else
{
lean_dec(v_i_1478_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1487_, lean_object* v_i_1488_, lean_object* v_k_1489_){
_start:
{
uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_res_1490_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1487_, v_i_1488_, v_k_1489_);
lean_dec(v_k_1489_);
lean_dec_ref(v_keys_1487_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(lean_object* v_x_1492_, size_t v_x_1493_, lean_object* v_x_1494_){
_start:
{
if (lean_obj_tag(v_x_1492_) == 0)
{
lean_object* v_es_1495_; lean_object* v___x_1496_; size_t v___x_1497_; size_t v___x_1498_; lean_object* v_j_1499_; lean_object* v___x_1500_; 
v_es_1495_ = lean_ctor_get(v_x_1492_, 0);
v___x_1496_ = lean_box(2);
v___x_1497_ = ((size_t)31ULL);
v___x_1498_ = lean_usize_land(v_x_1493_, v___x_1497_);
v_j_1499_ = lean_usize_to_nat(v___x_1498_);
v___x_1500_ = lean_array_get_borrowed(v___x_1496_, v_es_1495_, v_j_1499_);
lean_dec(v_j_1499_);
switch(lean_obj_tag(v___x_1500_))
{
case 0:
{
lean_object* v_key_1501_; uint8_t v___x_1502_; 
v_key_1501_ = lean_ctor_get(v___x_1500_, 0);
v___x_1502_ = lean_name_eq(v_x_1494_, v_key_1501_);
return v___x_1502_;
}
case 1:
{
lean_object* v_node_1503_; size_t v___x_1504_; size_t v___x_1505_; 
v_node_1503_ = lean_ctor_get(v___x_1500_, 0);
v___x_1504_ = ((size_t)5ULL);
v___x_1505_ = lean_usize_shift_right(v_x_1493_, v___x_1504_);
v_x_1492_ = v_node_1503_;
v_x_1493_ = v___x_1505_;
goto _start;
}
default: 
{
uint8_t v___x_1507_; 
v___x_1507_ = 0;
return v___x_1507_;
}
}
}
else
{
lean_object* v_ks_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_ks_1508_ = lean_ctor_get(v_x_1492_, 0);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_ks_1508_, v___x_1509_, v_x_1494_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(lean_object* v_x_1511_, lean_object* v_x_1512_, lean_object* v_x_1513_){
_start:
{
size_t v_x_1321__boxed_1514_; uint8_t v_res_1515_; lean_object* v_r_1516_; 
v_x_1321__boxed_1514_ = lean_unbox_usize(v_x_1512_);
lean_dec(v_x_1512_);
v_res_1515_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1511_, v_x_1321__boxed_1514_, v_x_1513_);
lean_dec(v_x_1513_);
lean_dec_ref(v_x_1511_);
v_r_1516_ = lean_box(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
uint64_t v___y_1520_; 
if (lean_obj_tag(v_x_1518_) == 0)
{
uint64_t v___x_1523_; 
v___x_1523_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1520_ = v___x_1523_;
goto v___jp_1519_;
}
else
{
uint64_t v_hash_1524_; 
v_hash_1524_ = lean_ctor_get_uint64(v_x_1518_, sizeof(void*)*2);
v___y_1520_ = v_hash_1524_;
goto v___jp_1519_;
}
v___jp_1519_:
{
size_t v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = lean_uint64_to_usize(v___y_1520_);
v___x_1522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1517_, v___x_1521_, v_x_1518_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(lean_object* v_x_1525_, lean_object* v_x_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1525_, v_x_1526_);
lean_dec(v_x_1526_);
lean_dec_ref(v_x_1525_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(lean_object* v_f_1529_, lean_object* v_keys_1530_, lean_object* v_vals_1531_, lean_object* v_i_1532_, lean_object* v_acc_1533_){
_start:
{
lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1534_ = lean_array_get_size(v_keys_1530_);
v___x_1535_ = lean_nat_dec_lt(v_i_1532_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_dec(v_i_1532_);
lean_dec(v_f_1529_);
return v_acc_1533_;
}
else
{
lean_object* v_k_1536_; lean_object* v_v_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_k_1536_ = lean_array_fget_borrowed(v_keys_1530_, v_i_1532_);
v_v_1537_ = lean_array_fget_borrowed(v_vals_1531_, v_i_1532_);
lean_inc(v_f_1529_);
lean_inc(v_v_1537_);
lean_inc(v_k_1536_);
v___x_1538_ = lean_apply_3(v_f_1529_, v_acc_1533_, v_k_1536_, v_v_1537_);
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_add(v_i_1532_, v___x_1539_);
lean_dec(v_i_1532_);
v_i_1532_ = v___x_1540_;
v_acc_1533_ = v___x_1538_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_1542_, lean_object* v_keys_1543_, lean_object* v_vals_1544_, lean_object* v_i_1545_, lean_object* v_acc_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1542_, v_keys_1543_, v_vals_1544_, v_i_1545_, v_acc_1546_);
lean_dec_ref(v_vals_1544_);
lean_dec_ref(v_keys_1543_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(lean_object* v_f_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_){
_start:
{
if (lean_obj_tag(v_x_1549_) == 0)
{
lean_object* v_es_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_es_1551_ = lean_ctor_get(v_x_1549_, 0);
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_array_get_size(v_es_1551_);
v___x_1554_ = lean_nat_dec_lt(v___x_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_dec(v_f_1548_);
return v_x_1550_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_nat_dec_le(v___x_1553_, v___x_1553_);
if (v___x_1555_ == 0)
{
if (v___x_1554_ == 0)
{
lean_dec(v_f_1548_);
return v_x_1550_;
}
else
{
size_t v___x_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = ((size_t)0ULL);
v___x_1557_ = lean_usize_of_nat(v___x_1553_);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1548_, v_es_1551_, v___x_1556_, v___x_1557_, v_x_1550_);
return v___x_1558_;
}
}
else
{
size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = lean_usize_of_nat(v___x_1553_);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1548_, v_es_1551_, v___x_1559_, v___x_1560_, v_x_1550_);
return v___x_1561_;
}
}
}
else
{
lean_object* v_ks_1562_; lean_object* v_vs_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_ks_1562_ = lean_ctor_get(v_x_1549_, 0);
v_vs_1563_ = lean_ctor_get(v_x_1549_, 1);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1548_, v_ks_1562_, v_vs_1563_, v___x_1564_, v_x_1550_);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1566_, lean_object* v_as_1567_, size_t v_i_1568_, size_t v_stop_1569_, lean_object* v_b_1570_){
_start:
{
lean_object* v___y_1572_; uint8_t v___x_1576_; 
v___x_1576_ = lean_usize_dec_eq(v_i_1568_, v_stop_1569_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_array_uget_borrowed(v_as_1567_, v_i_1568_);
switch(lean_obj_tag(v___x_1577_))
{
case 0:
{
lean_object* v_key_1578_; lean_object* v_val_1579_; lean_object* v___x_1580_; 
v_key_1578_ = lean_ctor_get(v___x_1577_, 0);
v_val_1579_ = lean_ctor_get(v___x_1577_, 1);
lean_inc(v_f_1566_);
lean_inc(v_val_1579_);
lean_inc(v_key_1578_);
v___x_1580_ = lean_apply_3(v_f_1566_, v_b_1570_, v_key_1578_, v_val_1579_);
v___y_1572_ = v___x_1580_;
goto v___jp_1571_;
}
case 1:
{
lean_object* v_node_1581_; lean_object* v___x_1582_; 
v_node_1581_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_f_1566_);
v___x_1582_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1566_, v_node_1581_, v_b_1570_);
v___y_1572_ = v___x_1582_;
goto v___jp_1571_;
}
default: 
{
v___y_1572_ = v_b_1570_;
goto v___jp_1571_;
}
}
}
else
{
lean_dec(v_f_1566_);
return v_b_1570_;
}
v___jp_1571_:
{
size_t v___x_1573_; size_t v___x_1574_; 
v___x_1573_ = ((size_t)1ULL);
v___x_1574_ = lean_usize_add(v_i_1568_, v___x_1573_);
v_i_1568_ = v___x_1574_;
v_b_1570_ = v___y_1572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1583_, lean_object* v_as_1584_, lean_object* v_i_1585_, lean_object* v_stop_1586_, lean_object* v_b_1587_){
_start:
{
size_t v_i_boxed_1588_; size_t v_stop_boxed_1589_; lean_object* v_res_1590_; 
v_i_boxed_1588_ = lean_unbox_usize(v_i_1585_);
lean_dec(v_i_1585_);
v_stop_boxed_1589_ = lean_unbox_usize(v_stop_1586_);
lean_dec(v_stop_1586_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1583_, v_as_1584_, v_i_boxed_1588_, v_stop_boxed_1589_, v_b_1587_);
lean_dec_ref(v_as_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(lean_object* v_f_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1591_, v_x_1592_, v_x_1593_);
lean_dec_ref(v_x_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object* v_d_1595_, lean_object* v_declName_1596_){
_start:
{
lean_object* v_tree_1597_; lean_object* v_erased_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_tree_1597_ = lean_ctor_get(v_d_1595_, 0);
v_erased_1598_ = lean_ctor_get(v_d_1595_, 1);
lean_inc(v_declName_1596_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1599_, 0, v_declName_1596_);
v___f_1600_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1600_, 0, v___f_1599_);
v___x_1601_ = 0;
v___x_1602_ = lean_box(v___x_1601_);
v___x_1603_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v___f_1600_, v_tree_1597_, v___x_1602_);
v___x_1604_ = lean_unbox(v___x_1603_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; 
lean_dec(v_declName_1596_);
v___x_1605_ = lean_unbox(v___x_1603_);
lean_dec(v___x_1603_);
return v___x_1605_;
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_erased_1598_, v_declName_1596_);
lean_dec(v_declName_1596_);
if (v___x_1606_ == 0)
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_unbox(v___x_1603_);
lean_dec(v___x_1603_);
return v___x_1607_;
}
else
{
lean_dec(v___x_1603_);
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object* v_d_1608_, lean_object* v_declName_1609_){
_start:
{
uint8_t v_res_1610_; lean_object* v_r_1611_; 
v_res_1610_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1608_, v_declName_1609_);
lean_dec_ref(v_d_1608_);
v_r_1611_ = lean_box(v_res_1610_);
return v_r_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(lean_object* v_00_u03c3_1612_, lean_object* v_00_u03b1_1613_, lean_object* v_f_1614_, lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1614_, v_x_1615_, v_x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(lean_object* v_00_u03c3_1618_, lean_object* v_00_u03b1_1619_, lean_object* v_f_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(v_00_u03c3_1618_, v_00_u03b1_1619_, v_f_1620_, v_x_1621_, v_x_1622_);
lean_dec_ref(v_x_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(lean_object* v_map_1624_, lean_object* v_f_1625_, lean_object* v_init_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1625_, v_map_1624_, v_init_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(lean_object* v_map_1628_, lean_object* v_f_1629_, lean_object* v_init_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(v_map_1628_, v_f_1629_, v_init_1630_);
lean_dec_ref(v_map_1628_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(lean_object* v_00_u03c3_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_map_1634_, lean_object* v_f_1635_, lean_object* v_init_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1635_, v_map_1634_, v_init_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(lean_object* v_00_u03c3_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_map_1640_, lean_object* v_f_1641_, lean_object* v_init_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(v_00_u03c3_1638_, v_00_u03b2_1639_, v_map_1640_, v_f_1641_, v_init_1642_);
lean_dec_ref(v_map_1640_);
return v_res_1643_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(lean_object* v_00_u03b2_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1645_, v_x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(lean_object* v_00_u03b2_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_){
_start:
{
uint8_t v_res_1651_; lean_object* v_r_1652_; 
v_res_1651_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(v_00_u03b2_1648_, v_x_1649_, v_x_1650_);
lean_dec(v_x_1650_);
lean_dec_ref(v_x_1649_);
v_r_1652_ = lean_box(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03c3_1654_, lean_object* v_f_1655_, lean_object* v_as_1656_, size_t v_i_1657_, size_t v_stop_1658_, lean_object* v_b_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1655_, v_as_1656_, v_i_1657_, v_stop_1658_, v_b_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1661_, lean_object* v_00_u03c3_1662_, lean_object* v_f_1663_, lean_object* v_as_1664_, lean_object* v_i_1665_, lean_object* v_stop_1666_, lean_object* v_b_1667_){
_start:
{
size_t v_i_boxed_1668_; size_t v_stop_boxed_1669_; lean_object* v_res_1670_; 
v_i_boxed_1668_ = lean_unbox_usize(v_i_1665_);
lean_dec(v_i_1665_);
v_stop_boxed_1669_ = lean_unbox_usize(v_stop_1666_);
lean_dec(v_stop_1666_);
v_res_1670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_00_u03b1_1661_, v_00_u03c3_1662_, v_f_1663_, v_as_1664_, v_i_boxed_1668_, v_stop_boxed_1669_, v_b_1667_);
lean_dec_ref(v_as_1664_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(lean_object* v_00_u03b1_1671_, lean_object* v_00_u03c3_1672_, lean_object* v_f_1673_, lean_object* v_as_1674_, size_t v_i_1675_, size_t v_stop_1676_, lean_object* v_b_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1673_, v_as_1674_, v_i_1675_, v_stop_1676_, v_b_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03c3_1680_, lean_object* v_f_1681_, lean_object* v_as_1682_, lean_object* v_i_1683_, lean_object* v_stop_1684_, lean_object* v_b_1685_){
_start:
{
size_t v_i_boxed_1686_; size_t v_stop_boxed_1687_; lean_object* v_res_1688_; 
v_i_boxed_1686_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_stop_boxed_1687_ = lean_unbox_usize(v_stop_1684_);
lean_dec(v_stop_1684_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(v_00_u03b1_1679_, v_00_u03c3_1680_, v_f_1681_, v_as_1682_, v_i_boxed_1686_, v_stop_boxed_1687_, v_b_1685_);
lean_dec_ref(v_as_1682_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(lean_object* v_00_u03c3_1689_, lean_object* v_00_u03b1_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_f_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1692_, v_x_1693_, v_x_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1696_, lean_object* v_00_u03b1_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_f_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(v_00_u03c3_1696_, v_00_u03b1_1697_, v_00_u03b2_1698_, v_f_1699_, v_x_1700_, v_x_1701_);
lean_dec_ref(v_x_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(lean_object* v_00_u03b2_1703_, lean_object* v_x_1704_, size_t v_x_1705_, lean_object* v_x_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1704_, v_x_1705_, v_x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1708_, lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
size_t v_x_1503__boxed_1712_; uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_x_1503__boxed_1712_ = lean_unbox_usize(v_x_1710_);
lean_dec(v_x_1710_);
v_res_1713_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(v_00_u03b2_1708_, v_x_1709_, v_x_1503__boxed_1712_, v_x_1711_);
lean_dec(v_x_1711_);
lean_dec_ref(v_x_1709_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_00_u03c3_1717_, lean_object* v_f_1718_, lean_object* v_as_1719_, size_t v_i_1720_, size_t v_stop_1721_, lean_object* v_b_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1718_, v_as_1719_, v_i_1720_, v_stop_1721_, v_b_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_00_u03c3_1726_, lean_object* v_f_1727_, lean_object* v_as_1728_, lean_object* v_i_1729_, lean_object* v_stop_1730_, lean_object* v_b_1731_){
_start:
{
size_t v_i_boxed_1732_; size_t v_stop_boxed_1733_; lean_object* v_res_1734_; 
v_i_boxed_1732_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_stop_boxed_1733_ = lean_unbox_usize(v_stop_1730_);
lean_dec(v_stop_1730_);
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(v_00_u03b1_1724_, v_00_u03b2_1725_, v_00_u03c3_1726_, v_f_1727_, v_as_1728_, v_i_boxed_1732_, v_stop_boxed_1733_, v_b_1731_);
lean_dec_ref(v_as_1728_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1735_, lean_object* v_00_u03b1_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_f_1738_, lean_object* v_keys_1739_, lean_object* v_vals_1740_, lean_object* v_heq_1741_, lean_object* v_i_1742_, lean_object* v_acc_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1738_, v_keys_1739_, v_vals_1740_, v_i_1742_, v_acc_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1745_, lean_object* v_00_u03b1_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_f_1748_, lean_object* v_keys_1749_, lean_object* v_vals_1750_, lean_object* v_heq_1751_, lean_object* v_i_1752_, lean_object* v_acc_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(v_00_u03c3_1745_, v_00_u03b1_1746_, v_00_u03b2_1747_, v_f_1748_, v_keys_1749_, v_vals_1750_, v_heq_1751_, v_i_1752_, v_acc_1753_);
lean_dec_ref(v_vals_1750_);
lean_dec_ref(v_keys_1749_);
return v_res_1754_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1755_, lean_object* v_keys_1756_, lean_object* v_vals_1757_, lean_object* v_heq_1758_, lean_object* v_i_1759_, lean_object* v_k_1760_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1756_, v_i_1759_, v_k_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1762_, lean_object* v_keys_1763_, lean_object* v_vals_1764_, lean_object* v_heq_1765_, lean_object* v_i_1766_, lean_object* v_k_1767_){
_start:
{
uint8_t v_res_1768_; lean_object* v_r_1769_; 
v_res_1768_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(v_00_u03b2_1762_, v_keys_1763_, v_vals_1764_, v_heq_1765_, v_i_1766_, v_k_1767_);
lean_dec(v_k_1767_);
lean_dec_ref(v_vals_1764_);
lean_dec_ref(v_keys_1763_);
v_r_1769_ = lean_box(v_res_1768_);
return v_r_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg(lean_object* v_declName_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v___x_1773_; lean_object* v_env_1774_; lean_object* v___x_1775_; lean_object* v_ext_1776_; lean_object* v_toEnvExtension_1777_; lean_object* v_asyncMode_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1773_ = lean_st_ref_get(v_a_1771_);
v_env_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc_ref(v_env_1774_);
lean_dec(v___x_1773_);
v___x_1775_ = l_Lean_Meta_Ext_extExtension;
v_ext_1776_ = lean_ctor_get(v___x_1775_, 1);
v_toEnvExtension_1777_ = lean_ctor_get(v_ext_1776_, 0);
v_asyncMode_1778_ = lean_ctor_get(v_toEnvExtension_1777_, 2);
v___x_1779_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1780_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1779_, v___x_1775_, v_env_1774_, v_asyncMode_1778_);
v___x_1781_ = l_Lean_Meta_Ext_ExtTheorems_contains(v___x_1780_, v_declName_1770_);
lean_dec(v___x_1780_);
v___x_1782_ = lean_box(v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg___boxed(lean_object* v_declName_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1784_, v_a_1785_);
lean_dec(v_a_1785_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object* v_declName_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1788_, v_a_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object* v_declName_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Meta_Ext_isExtTheorem(v_declName_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(lean_object* v_d_1798_, lean_object* v_declName_1799_, lean_object* v_toPure_1800_, lean_object* v_____r_1801_){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = l_Lean_Meta_Ext_ExtTheorems_eraseCore(v_d_1798_, v_declName_1799_);
v___x_1803_ = lean_apply_2(v_toPure_1800_, lean_box(0), v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1(lean_object* v___f_1804_, lean_object* v_____r_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_apply_1(v___f_1804_, v_____r_1805_);
return v___x_1806_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0));
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2));
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg(lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_d_1815_, lean_object* v_declName_1816_){
_start:
{
lean_object* v_toApplicative_1817_; lean_object* v_toBind_1818_; lean_object* v_toPure_1819_; lean_object* v___f_1820_; uint8_t v___x_1821_; 
v_toApplicative_1817_ = lean_ctor_get(v_inst_1813_, 0);
v_toBind_1818_ = lean_ctor_get(v_inst_1813_, 1);
lean_inc(v_toBind_1818_);
v_toPure_1819_ = lean_ctor_get(v_toApplicative_1817_, 1);
lean_inc(v_toPure_1819_);
lean_inc_n(v_declName_1816_, 2);
lean_inc_ref(v_d_1815_);
v___f_1820_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1820_, 0, v_d_1815_);
lean_closure_set(v___f_1820_, 1, v_declName_1816_);
lean_closure_set(v___f_1820_, 2, v_toPure_1819_);
v___x_1821_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1815_, v_declName_1816_);
if (v___x_1821_ == 0)
{
lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_d_1815_);
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1822_, 0, v___f_1820_);
v___x_1823_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1);
v___x_1824_ = l_Lean_MessageData_ofConstName(v_declName_1816_, v___x_1821_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_throwError___redArg(v_inst_1813_, v_inst_1814_, v___x_1827_);
v___x_1829_ = lean_apply_4(v_toBind_1818_, lean_box(0), lean_box(0), v___x_1828_, v___f_1822_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_inc(v_toPure_1819_);
lean_dec_ref(v___f_1820_);
lean_dec(v_toBind_1818_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
v___x_1830_ = lean_box(0);
v___x_1831_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(v_d_1815_, v_declName_1816_, v_toPure_1819_, v___x_1830_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object* v_m_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_d_1835_, lean_object* v_declName_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg(v_inst_1833_, v_inst_1834_, v_d_1835_, v_declName_1836_);
return v___x_1837_;
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
