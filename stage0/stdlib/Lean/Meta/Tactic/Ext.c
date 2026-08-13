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
LEAN_EXPORT uint64_t l_Lean_Meta_Ext_instHashableExtTheorem_hash(lean_object* v_x_240_){
_start:
{
lean_object* v_declName_241_; lean_object* v_priority_242_; lean_object* v_keys_243_; uint64_t v___x_244_; uint64_t v___y_246_; 
v_declName_241_ = lean_ctor_get(v_x_240_, 0);
v_priority_242_ = lean_ctor_get(v_x_240_, 1);
v_keys_243_ = lean_ctor_get(v_x_240_, 2);
v___x_244_ = 0ULL;
if (lean_obj_tag(v_declName_241_) == 0)
{
uint64_t v___x_265_; 
v___x_265_ = 1723ULL;
v___y_246_ = v___x_265_;
goto v___jp_245_;
}
else
{
uint64_t v_hash_266_; 
v_hash_266_ = lean_ctor_get_uint64(v_declName_241_, sizeof(void*)*2);
v___y_246_ = v_hash_266_;
goto v___jp_245_;
}
v___jp_245_:
{
uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_247_ = lean_uint64_mix_hash(v___x_244_, v___y_246_);
v___x_248_ = lean_uint64_of_nat(v_priority_242_);
v___x_249_ = lean_uint64_mix_hash(v___x_247_, v___x_248_);
v___x_250_ = 7ULL;
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_array_get_size(v_keys_243_);
v___x_253_ = lean_nat_dec_lt(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
uint64_t v___x_254_; 
v___x_254_ = lean_uint64_mix_hash(v___x_249_, v___x_250_);
return v___x_254_;
}
else
{
uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_le(v___x_252_, v___x_252_);
if (v___x_255_ == 0)
{
if (v___x_253_ == 0)
{
uint64_t v___x_256_; 
v___x_256_ = lean_uint64_mix_hash(v___x_249_, v___x_250_);
return v___x_256_;
}
else
{
size_t v___x_257_; size_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; 
v___x_257_ = ((size_t)0ULL);
v___x_258_ = lean_usize_of_nat(v___x_252_);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_keys_243_, v___x_257_, v___x_258_, v___x_250_);
v___x_260_ = lean_uint64_mix_hash(v___x_249_, v___x_259_);
return v___x_260_;
}
}
else
{
size_t v___x_261_; size_t v___x_262_; uint64_t v___x_263_; uint64_t v___x_264_; 
v___x_261_ = ((size_t)0ULL);
v___x_262_ = lean_usize_of_nat(v___x_252_);
v___x_263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_keys_243_, v___x_261_, v___x_262_, v___x_250_);
v___x_264_ = lean_uint64_mix_hash(v___x_249_, v___x_263_);
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instHashableExtTheorem_hash___boxed(lean_object* v_x_267_){
_start:
{
uint64_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l_Lean_Meta_Ext_instHashableExtTheorem_hash(v_x_267_);
lean_dec_ref(v_x_267_);
v_r_269_ = lean_box_uint64(v_res_268_);
return v_r_269_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_272_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(lean_object* v_00_u03b2_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__1);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(lean_box(0));
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__2);
v___x_282_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default(void){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_288_, 0, v_a_287_);
lean_inc_ref_n(v___x_288_, 2);
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_x_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v_x_290_, v_a_291_);
lean_dec_ref(v_x_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15(lean_object* v_xs_293_, lean_object* v_v_294_, lean_object* v_i_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_array_get_size(v_xs_293_);
v___x_297_ = lean_nat_dec_lt(v_i_295_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec(v_i_295_);
v___x_298_ = lean_box(0);
return v___x_298_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_array_fget_borrowed(v_xs_293_, v_i_295_);
v___x_300_ = lean_name_eq(v___x_299_, v_v_294_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_i_295_, v___x_301_);
lean_dec(v_i_295_);
v_i_295_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_i_295_);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15___boxed(lean_object* v_xs_305_, lean_object* v_v_306_, lean_object* v_i_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15(v_xs_305_, v_v_306_, v_i_307_);
lean_dec(v_v_306_);
lean_dec_ref(v_xs_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9(lean_object* v_xs_309_, lean_object* v_v_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9_spec__15(v_xs_309_, v_v_310_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9___boxed(lean_object* v_xs_313_, lean_object* v_v_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_xs_313_, v_v_314_);
lean_dec(v_v_314_);
lean_dec_ref(v_xs_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_x_316_, size_t v_x_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v_es_319_; lean_object* v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v_j_323_; lean_object* v_entry_324_; 
v_es_319_ = lean_ctor_get(v_x_316_, 0);
v___x_320_ = lean_box(2);
v___x_321_ = ((size_t)31ULL);
v___x_322_ = lean_usize_land(v_x_317_, v___x_321_);
v_j_323_ = lean_usize_to_nat(v___x_322_);
v_entry_324_ = lean_array_get(v___x_320_, v_es_319_, v_j_323_);
switch(lean_obj_tag(v_entry_324_))
{
case 0:
{
lean_object* v_key_325_; uint8_t v___x_326_; 
v_key_325_ = lean_ctor_get(v_entry_324_, 0);
lean_inc(v_key_325_);
lean_dec_ref_known(v_entry_324_, 2);
v___x_326_ = lean_name_eq(v_x_318_, v_key_325_);
lean_dec(v_key_325_);
if (v___x_326_ == 0)
{
lean_dec(v_j_323_);
return v_x_316_;
}
else
{
lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
lean_inc_ref(v_es_319_);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_x_316_, 0);
lean_dec(v_unused_335_);
v___x_328_ = v_x_316_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_dec(v_x_316_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_array_set(v_es_319_, v_j_323_, v___x_320_);
lean_dec(v_j_323_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
case 1:
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_370_; 
lean_inc_ref(v_es_319_);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v_x_316_, 0);
lean_dec(v_unused_371_);
v___x_337_ = v_x_316_;
v_isShared_338_ = v_isSharedCheck_370_;
goto v_resetjp_336_;
}
else
{
lean_dec(v_x_316_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_370_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_node_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_369_; 
v_node_339_ = lean_ctor_get(v_entry_324_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_entry_324_);
if (v_isSharedCheck_369_ == 0)
{
v___x_341_ = v_entry_324_;
v_isShared_342_ = v_isSharedCheck_369_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_node_339_);
lean_dec(v_entry_324_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_369_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
size_t v___x_343_; lean_object* v_entries_344_; size_t v___x_345_; lean_object* v_newNode_346_; lean_object* v___x_347_; 
v___x_343_ = ((size_t)5ULL);
v_entries_344_ = lean_array_set(v_es_319_, v_j_323_, v___x_320_);
v___x_345_ = lean_usize_shift_right(v_x_317_, v___x_343_);
v_newNode_346_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_node_339_, v___x_345_, v_x_318_);
lean_inc_ref(v_newNode_346_);
v___x_347_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v___x_349_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v_newNode_346_);
v___x_349_ = v___x_341_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_newNode_346_);
v___x_349_ = v_reuseFailAlloc_354_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_array_set(v_entries_344_, v_j_323_, v___x_349_);
lean_dec(v_j_323_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_350_);
v___x_352_ = v___x_337_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_val_355_; lean_object* v_fst_356_; lean_object* v_snd_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v_newNode_346_);
lean_del_object(v___x_341_);
v_val_355_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v___x_347_, 1);
v_fst_356_ = lean_ctor_get(v_val_355_, 0);
v_snd_357_ = lean_ctor_get(v_val_355_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_val_355_);
if (v_isSharedCheck_368_ == 0)
{
v___x_359_ = v_val_355_;
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snd_357_);
lean_inc(v_fst_356_);
lean_dec(v_val_355_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_368_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_fst_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_snd_357_);
v___x_362_ = v_reuseFailAlloc_367_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_array_set(v_entries_344_, v_j_323_, v___x_362_);
lean_dec(v_j_323_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_363_);
v___x_365_ = v___x_337_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_323_);
return v_x_316_;
}
}
}
else
{
lean_object* v_ks_372_; lean_object* v_vs_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_387_; 
v_ks_372_ = lean_ctor_get(v_x_316_, 0);
v_vs_373_ = lean_ctor_get(v_x_316_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_316_);
if (v_isSharedCheck_387_ == 0)
{
v___x_375_ = v_x_316_;
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_vs_373_);
lean_inc(v_ks_372_);
lean_dec(v_x_316_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_387_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; 
v___x_377_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__9(v_ks_372_, v_x_318_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v___x_379_; 
if (v_isShared_376_ == 0)
{
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_ks_372_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_vs_373_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
lean_object* v_val_381_; lean_object* v_keys_x27_382_; lean_object* v_vals_x27_383_; lean_object* v___x_385_; 
v_val_381_ = lean_ctor_get(v___x_377_, 0);
lean_inc_n(v_val_381_, 2);
lean_dec_ref_known(v___x_377_, 1);
v_keys_x27_382_ = l_Array_eraseIdx___redArg(v_ks_372_, v_val_381_);
v_vals_x27_383_ = l_Array_eraseIdx___redArg(v_vs_373_, v_val_381_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v_vals_x27_383_);
lean_ctor_set(v___x_375_, 0, v_keys_x27_382_);
v___x_385_ = v___x_375_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_keys_x27_382_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_vals_x27_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_x_388_, lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
size_t v_x_1794__boxed_391_; lean_object* v_res_392_; 
v_x_1794__boxed_391_ = lean_unbox_usize(v_x_389_);
lean_dec(v_x_389_);
v_res_392_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_388_, v_x_1794__boxed_391_, v_x_390_);
lean_dec(v_x_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
uint64_t v___y_396_; 
if (lean_obj_tag(v_x_394_) == 0)
{
uint64_t v___x_399_; 
v___x_399_ = 1723ULL;
v___y_396_ = v___x_399_;
goto v___jp_395_;
}
else
{
uint64_t v_hash_400_; 
v_hash_400_ = lean_ctor_get_uint64(v_x_394_, sizeof(void*)*2);
v___y_396_ = v_hash_400_;
goto v___jp_395_;
}
v___jp_395_:
{
size_t v_h_397_; lean_object* v___x_398_; 
v_h_397_ = lean_uint64_to_usize(v___y_396_);
v___x_398_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_393_, v_h_397_, v_x_394_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_401_, v_x_402_);
lean_dec(v_x_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_ks_408_; lean_object* v_vs_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_433_; 
v_ks_408_ = lean_ctor_get(v_x_404_, 0);
v_vs_409_ = lean_ctor_get(v_x_404_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_404_);
if (v_isSharedCheck_433_ == 0)
{
v___x_411_ = v_x_404_;
v_isShared_412_ = v_isSharedCheck_433_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_vs_409_);
lean_inc(v_ks_408_);
lean_dec(v_x_404_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_433_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_413_ = lean_array_get_size(v_ks_408_);
v___x_414_ = lean_nat_dec_lt(v_x_405_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
lean_dec(v_x_405_);
v___x_415_ = lean_array_push(v_ks_408_, v_x_406_);
v___x_416_ = lean_array_push(v_vs_409_, v_x_407_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_416_);
lean_ctor_set(v___x_411_, 0, v___x_415_);
v___x_418_ = v___x_411_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v_k_x27_420_; uint8_t v___x_421_; 
v_k_x27_420_ = lean_array_fget_borrowed(v_ks_408_, v_x_405_);
v___x_421_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_406_, v_k_x27_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_423_; 
if (v_isShared_412_ == 0)
{
v___x_423_ = v___x_411_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_ks_408_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_vs_409_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_add(v_x_405_, v___x_424_);
lean_dec(v_x_405_);
v_x_404_ = v___x_423_;
v_x_405_ = v___x_425_;
goto _start;
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = lean_array_fset(v_ks_408_, v_x_405_, v_x_406_);
v___x_429_ = lean_array_fset(v_vs_409_, v_x_405_, v_x_407_);
lean_dec(v_x_405_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_429_);
lean_ctor_set(v___x_411_, 0, v___x_428_);
v___x_431_ = v___x_411_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(lean_object* v_n_434_, lean_object* v_k_435_, lean_object* v_v_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(v_n_434_, v___x_437_, v_k_435_, v_v_436_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(lean_object* v_x_440_, size_t v_x_441_, size_t v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_object* v_es_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v_j_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_es_445_ = lean_ctor_get(v_x_440_, 0);
v___x_446_ = ((size_t)31ULL);
v___x_447_ = lean_usize_land(v_x_441_, v___x_446_);
v_j_448_ = lean_usize_to_nat(v___x_447_);
v___x_449_ = lean_array_get_size(v_es_445_);
v___x_450_ = lean_nat_dec_lt(v_j_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec(v_j_448_);
lean_dec(v_x_444_);
lean_dec(v_x_443_);
return v_x_440_;
}
else
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_489_; 
lean_inc_ref(v_es_445_);
v_isSharedCheck_489_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_x_440_, 0);
lean_dec(v_unused_490_);
v___x_452_ = v_x_440_;
v_isShared_453_ = v_isSharedCheck_489_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_x_440_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_489_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_v_454_; lean_object* v___x_455_; lean_object* v_xs_x27_456_; lean_object* v___y_458_; 
v_v_454_ = lean_array_fget(v_es_445_, v_j_448_);
v___x_455_ = lean_box(0);
v_xs_x27_456_ = lean_array_fset(v_es_445_, v_j_448_, v___x_455_);
switch(lean_obj_tag(v_v_454_))
{
case 0:
{
lean_object* v_key_463_; lean_object* v_val_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_474_; 
v_key_463_ = lean_ctor_get(v_v_454_, 0);
v_val_464_ = lean_ctor_get(v_v_454_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_v_454_);
if (v_isSharedCheck_474_ == 0)
{
v___x_466_ = v_v_454_;
v_isShared_467_ = v_isSharedCheck_474_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_val_464_);
lean_inc(v_key_463_);
lean_dec(v_v_454_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_474_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v___x_468_; 
v___x_468_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_443_, v_key_463_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_del_object(v___x_466_);
v___x_469_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_463_, v_val_464_, v_x_443_, v_x_444_);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
v___y_458_ = v___x_470_;
goto v___jp_457_;
}
else
{
lean_object* v___x_472_; 
lean_dec(v_val_464_);
lean_dec(v_key_463_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v_x_444_);
lean_ctor_set(v___x_466_, 0, v_x_443_);
v___x_472_ = v___x_466_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_x_443_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_x_444_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
v___y_458_ = v___x_472_;
goto v___jp_457_;
}
}
}
}
case 1:
{
lean_object* v_node_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_487_; 
v_node_475_ = lean_ctor_get(v_v_454_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_v_454_);
if (v_isSharedCheck_487_ == 0)
{
v___x_477_ = v_v_454_;
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_node_475_);
lean_dec(v_v_454_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_479_ = ((size_t)5ULL);
v___x_480_ = lean_usize_shift_right(v_x_441_, v___x_479_);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_add(v_x_442_, v___x_481_);
v___x_483_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_node_475_, v___x_480_, v___x_482_, v_x_443_, v_x_444_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_483_);
v___x_485_ = v___x_477_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
v___y_458_ = v___x_485_;
goto v___jp_457_;
}
}
}
default: 
{
lean_object* v___x_488_; 
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v_x_443_);
lean_ctor_set(v___x_488_, 1, v_x_444_);
v___y_458_ = v___x_488_;
goto v___jp_457_;
}
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_array_fset(v_xs_x27_456_, v_j_448_, v___y_458_);
lean_dec(v_j_448_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_459_);
v___x_461_ = v___x_452_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
else
{
lean_object* v_ks_491_; lean_object* v_vs_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_512_; 
v_ks_491_ = lean_ctor_get(v_x_440_, 0);
v_vs_492_ = lean_ctor_get(v_x_440_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_512_ == 0)
{
v___x_494_ = v_x_440_;
v_isShared_495_ = v_isSharedCheck_512_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_vs_492_);
lean_inc(v_ks_491_);
lean_dec(v_x_440_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_512_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_ks_491_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_vs_492_);
v___x_497_ = v_reuseFailAlloc_511_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v_newNode_498_; uint8_t v___y_500_; size_t v___x_506_; uint8_t v___x_507_; 
v_newNode_498_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(v___x_497_, v_x_443_, v_x_444_);
v___x_506_ = ((size_t)7ULL);
v___x_507_ = lean_usize_dec_le(v___x_506_, v_x_442_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_498_);
v___x_509_ = lean_unsigned_to_nat(4u);
v___x_510_ = lean_nat_dec_lt(v___x_508_, v___x_509_);
lean_dec(v___x_508_);
v___y_500_ = v___x_510_;
goto v___jp_499_;
}
else
{
v___y_500_ = v___x_507_;
goto v___jp_499_;
}
v___jp_499_:
{
if (v___y_500_ == 0)
{
lean_object* v_ks_501_; lean_object* v_vs_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_ks_501_ = lean_ctor_get(v_newNode_498_, 0);
lean_inc_ref(v_ks_501_);
v_vs_502_ = lean_ctor_get(v_newNode_498_, 1);
lean_inc_ref(v_vs_502_);
lean_dec_ref(v_newNode_498_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___closed__0);
v___x_505_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(v_x_442_, v_ks_501_, v_vs_502_, v___x_503_, v___x_504_);
lean_dec_ref(v_vs_502_);
lean_dec_ref(v_ks_501_);
return v___x_505_;
}
else
{
return v_newNode_498_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(size_t v_depth_513_, lean_object* v_keys_514_, lean_object* v_vals_515_, lean_object* v_i_516_, lean_object* v_entries_517_){
_start:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_array_get_size(v_keys_514_);
v___x_519_ = lean_nat_dec_lt(v_i_516_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v_i_516_);
return v_entries_517_;
}
else
{
lean_object* v_k_520_; lean_object* v_v_521_; uint64_t v___x_522_; size_t v_h_523_; size_t v___x_524_; lean_object* v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v_h_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_k_520_ = lean_array_fget_borrowed(v_keys_514_, v_i_516_);
v_v_521_ = lean_array_fget_borrowed(v_vals_515_, v_i_516_);
v___x_522_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_520_);
v_h_523_ = lean_uint64_to_usize(v___x_522_);
v___x_524_ = ((size_t)5ULL);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_sub(v_depth_513_, v___x_526_);
v___x_528_ = lean_usize_mul(v___x_524_, v___x_527_);
v_h_529_ = lean_usize_shift_right(v_h_523_, v___x_528_);
v___x_530_ = lean_nat_add(v_i_516_, v___x_525_);
lean_dec(v_i_516_);
lean_inc(v_v_521_);
lean_inc(v_k_520_);
v___x_531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_entries_517_, v_h_529_, v_depth_513_, v_k_520_, v_v_521_);
v_i_516_ = v___x_530_;
v_entries_517_ = v___x_531_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg___boxed(lean_object* v_depth_533_, lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_i_536_, lean_object* v_entries_537_){
_start:
{
size_t v_depth_boxed_538_; lean_object* v_res_539_; 
v_depth_boxed_538_ = lean_unbox_usize(v_depth_533_);
lean_dec(v_depth_533_);
v_res_539_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(v_depth_boxed_538_, v_keys_534_, v_vals_535_, v_i_536_, v_entries_537_);
lean_dec_ref(v_vals_535_);
lean_dec_ref(v_keys_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
size_t v_x_2020__boxed_545_; size_t v_x_2021__boxed_546_; lean_object* v_res_547_; 
v_x_2020__boxed_545_ = lean_unbox_usize(v_x_541_);
lean_dec(v_x_541_);
v_x_2021__boxed_546_ = lean_unbox_usize(v_x_542_);
lean_dec(v_x_542_);
v_res_547_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_x_540_, v_x_2020__boxed_545_, v_x_2021__boxed_546_, v_x_543_, v_x_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9(lean_object* v_xs_548_, lean_object* v_v_549_, lean_object* v_i_550_){
_start:
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_array_get_size(v_xs_548_);
v___x_552_ = lean_nat_dec_lt(v_i_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec(v_i_550_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_fget_borrowed(v_xs_548_, v_i_550_);
v___x_555_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_554_, v_v_549_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_add(v_i_550_, v___x_556_);
lean_dec(v_i_550_);
v_i_550_ = v___x_557_;
goto _start;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_i_550_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_xs_560_, lean_object* v_v_561_, lean_object* v_i_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9(v_xs_560_, v_v_561_, v_i_562_);
lean_dec(v_v_561_);
lean_dec_ref(v_xs_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(lean_object* v_xs_564_, lean_object* v_v_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__9(v_xs_564_, v_v_565_, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4___boxed(lean_object* v_xs_568_, lean_object* v_v_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(v_xs_568_, v_v_569_);
lean_dec(v_v_569_);
lean_dec_ref(v_xs_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(lean_object* v_x_571_, lean_object* v_keys_572_, lean_object* v_v_573_, lean_object* v_k_574_, lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_c_578_; lean_object* v___x_579_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_x_571_, v___x_576_);
v_c_578_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_572_, v_v_573_, v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_k_574_);
lean_ctor_set(v___x_579_, 1, v_c_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_580_, lean_object* v_keys_581_, lean_object* v_v_582_, lean_object* v_k_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_580_, v_keys_581_, v_v_582_, v_k_583_, v_x_584_);
lean_dec_ref(v_keys_581_);
lean_dec(v_x_580_);
return v_res_585_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(lean_object* v_a_586_, lean_object* v_b_587_){
_start:
{
lean_object* v_fst_588_; lean_object* v_fst_589_; uint8_t v___x_590_; 
v_fst_588_ = lean_ctor_get(v_a_586_, 0);
v_fst_589_ = lean_ctor_get(v_b_587_, 0);
v___x_590_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_588_, v_fst_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_591_, lean_object* v_b_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_a_591_, v_b_592_);
lean_dec_ref(v_b_592_);
lean_dec_ref(v_a_591_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_vs_595_, lean_object* v_v_596_, lean_object* v_i_597_){
_start:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_get_size(v_vs_595_);
v___x_599_ = lean_nat_dec_lt(v_i_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
lean_dec(v_i_597_);
v___x_600_ = lean_array_push(v_vs_595_, v_v_596_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_array_fget_borrowed(v_vs_595_, v_i_597_);
v___x_602_ = l_Lean_Meta_Ext_instBEqExtTheorem_beq(v_v_596_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_i_597_, v___x_603_);
lean_dec(v_i_597_);
v_i_597_ = v___x_604_;
goto _start;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_array_fset(v_vs_595_, v_i_597_, v_v_596_);
lean_dec(v_i_597_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_vs_607_, lean_object* v_v_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_vs_607_, v_v_608_, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_615_, lean_object* v_keys_616_, lean_object* v_v_617_, lean_object* v_k_618_, lean_object* v_as_619_, lean_object* v_k_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_mid_625_; lean_object* v_midVal_626_; uint8_t v___x_627_; 
v___x_623_ = lean_nat_add(v_x_621_, v_x_622_);
v___x_624_ = lean_unsigned_to_nat(1u);
v_mid_625_ = lean_nat_shiftr(v___x_623_, v___x_624_);
lean_dec(v___x_623_);
v_midVal_626_ = lean_array_fget(v_as_619_, v_mid_625_);
v___x_627_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_midVal_626_, v_k_620_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; 
lean_dec(v_x_622_);
v___x_628_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_k_620_, v_midVal_626_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; uint8_t v___x_630_; 
lean_dec(v_x_621_);
v___x_629_ = lean_array_get_size(v_as_619_);
v___x_630_ = lean_nat_dec_lt(v_mid_625_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v_midVal_626_);
lean_dec(v_mid_625_);
lean_dec(v_k_618_);
lean_dec_ref(v_v_617_);
return v_as_619_;
}
else
{
lean_object* v_snd_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_643_; 
v_snd_631_ = lean_ctor_get(v_midVal_626_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_midVal_626_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v_midVal_626_, 0);
lean_dec(v_unused_644_);
v___x_633_ = v_midVal_626_;
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_snd_631_);
lean_dec(v_midVal_626_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v_xs_x27_636_; lean_object* v___x_637_; lean_object* v_c_638_; lean_object* v___x_640_; 
v___x_635_ = lean_box(0);
v_xs_x27_636_ = lean_array_fset(v_as_619_, v_mid_625_, v___x_635_);
v___x_637_ = lean_nat_add(v_x_615_, v___x_624_);
v_c_638_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_616_, v_v_617_, v___x_637_, v_snd_631_);
lean_dec(v___x_637_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_c_638_);
lean_ctor_set(v___x_633_, 0, v_k_618_);
v___x_640_ = v___x_633_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_k_618_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_c_638_);
v___x_640_ = v_reuseFailAlloc_642_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; 
v___x_641_ = lean_array_fset(v_xs_x27_636_, v_mid_625_, v___x_640_);
lean_dec(v_mid_625_);
return v___x_641_;
}
}
}
}
else
{
lean_dec(v_midVal_626_);
v_x_622_ = v_mid_625_;
goto _start;
}
}
else
{
uint8_t v___x_646_; 
lean_dec(v_midVal_626_);
v___x_646_ = lean_nat_dec_eq(v_mid_625_, v_x_621_);
if (v___x_646_ == 0)
{
lean_dec(v_x_621_);
v_x_621_ = v_mid_625_;
goto _start;
}
else
{
lean_object* v___x_648_; lean_object* v_c_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v_j_652_; lean_object* v_as_653_; lean_object* v___x_654_; 
lean_dec(v_mid_625_);
lean_dec(v_x_622_);
v___x_648_ = lean_nat_add(v_x_615_, v___x_624_);
v_c_649_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_616_, v_v_617_, v___x_648_);
lean_dec(v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_k_618_);
lean_ctor_set(v___x_650_, 1, v_c_649_);
v___x_651_ = lean_nat_add(v_x_621_, v___x_624_);
lean_dec(v_x_621_);
v_j_652_ = lean_array_get_size(v_as_619_);
v_as_653_ = lean_array_push(v_as_619_, v___x_650_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_651_, v_as_653_, v_j_652_);
lean_dec(v___x_651_);
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_x_655_, lean_object* v_keys_656_, lean_object* v_v_657_, lean_object* v_k_658_, lean_object* v_as_659_, lean_object* v_k_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = lean_array_get_size(v_as_659_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_nat_dec_eq(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_array_fget_borrowed(v_as_659_, v___x_662_);
v___x_665_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_k_660_, v___x_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v___x_664_, v_k_660_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_lt(v___x_662_, v___x_661_);
if (v___x_667_ == 0)
{
lean_dec(v_k_658_);
lean_dec_ref(v_v_657_);
return v_as_659_;
}
else
{
lean_object* v___x_668_; lean_object* v_xs_x27_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_inc(v___x_664_);
v___x_668_ = lean_box(0);
v_xs_x27_669_ = lean_array_fset(v_as_659_, v___x_662_, v___x_668_);
v___x_670_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_655_, v_keys_656_, v_v_657_, v_k_658_, v___x_664_);
v___x_671_ = lean_array_fset(v_xs_x27_669_, v___x_662_, v___x_670_);
return v___x_671_;
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_sub(v___x_661_, v___x_672_);
v___x_674_ = lean_array_fget_borrowed(v_as_659_, v___x_673_);
v___x_675_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v___x_674_, v_k_660_);
if (v___x_675_ == 0)
{
uint8_t v___x_676_; 
v___x_676_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__1(v_k_660_, v___x_674_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_lt(v___x_673_, v___x_661_);
if (v___x_677_ == 0)
{
lean_dec(v___x_673_);
lean_dec(v_k_658_);
lean_dec_ref(v_v_657_);
return v_as_659_;
}
else
{
lean_object* v___x_678_; lean_object* v_xs_x27_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_inc(v___x_674_);
v___x_678_ = lean_box(0);
v_xs_x27_679_ = lean_array_fset(v_as_659_, v___x_673_, v___x_678_);
v___x_680_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_655_, v_keys_656_, v_v_657_, v_k_658_, v___x_674_);
v___x_681_ = lean_array_fset(v_xs_x27_679_, v___x_673_, v___x_680_);
lean_dec(v___x_673_);
return v___x_681_;
}
}
else
{
lean_object* v___x_682_; 
v___x_682_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_655_, v_keys_656_, v_v_657_, v_k_658_, v_as_659_, v_k_660_, v___x_662_, v___x_673_);
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec(v___x_673_);
v___x_683_ = lean_box(0);
v___x_684_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_655_, v_keys_656_, v_v_657_, v_k_658_, v___x_683_);
v___x_685_ = lean_array_push(v_as_659_, v___x_684_);
return v___x_685_;
}
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_as_688_; lean_object* v___x_689_; 
v___x_686_ = lean_box(0);
v___x_687_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_655_, v_keys_656_, v_v_657_, v_k_658_, v___x_686_);
v_as_688_ = lean_array_push(v_as_659_, v___x_687_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_662_, v_as_688_, v___x_661_);
return v___x_689_;
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__0(v_x_655_, v_keys_656_, v_v_657_, v_k_658_, v___x_690_);
v___x_692_ = lean_array_push(v_as_659_, v___x_691_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_keys_693_, lean_object* v_v_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_vs_697_; lean_object* v_children_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_715_; 
v_vs_697_ = lean_ctor_get(v_x_696_, 0);
v_children_698_ = lean_ctor_get(v_x_696_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_715_ == 0)
{
v___x_700_ = v_x_696_;
v_isShared_701_ = v_isSharedCheck_715_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_children_698_);
lean_inc(v_vs_697_);
lean_dec(v_x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_715_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_array_get_size(v_keys_693_);
v___x_703_ = lean_nat_dec_lt(v_x_695_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_vs_697_, v_v_694_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_704_);
v___x_706_ = v___x_700_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_children_698_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_object* v_k_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_c_711_; lean_object* v___x_713_; 
v_k_708_ = lean_array_fget_borrowed(v_keys_693_, v_x_695_);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1));
lean_inc_n(v_k_708_, 2);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_k_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v_c_711_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_x_695_, v_keys_693_, v_v_694_, v_k_708_, v_children_698_, v___x_710_);
lean_dec_ref_known(v___x_710_, 2);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v_c_711_);
v___x_713_ = v___x_700_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_vs_697_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_c_711_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(lean_object* v_x_716_, lean_object* v_keys_717_, lean_object* v_v_718_, lean_object* v_k_719_, lean_object* v_x_720_){
_start:
{
lean_object* v_snd_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_731_; 
v_snd_721_ = lean_ctor_get(v_x_720_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_x_720_, 0);
lean_dec(v_unused_732_);
v___x_723_ = v_x_720_;
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snd_721_);
lean_dec(v_x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_c_727_; lean_object* v___x_729_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_x_716_, v___x_725_);
v_c_727_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_717_, v_v_718_, v___x_726_, v_snd_721_);
lean_dec(v___x_726_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v_c_727_);
lean_ctor_set(v___x_723_, 0, v_k_719_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_k_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_c_727_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_733_, lean_object* v_keys_734_, lean_object* v_v_735_, lean_object* v_k_736_, lean_object* v_x_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___lam__2(v_x_733_, v_keys_734_, v_v_735_, v_k_736_, v_x_737_);
lean_dec_ref(v_keys_734_);
lean_dec(v_x_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_keys_739_, lean_object* v_v_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_739_, v_v_740_, v_x_741_, v_x_742_);
lean_dec(v_x_741_);
lean_dec_ref(v_keys_739_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_x_744_, lean_object* v_keys_745_, lean_object* v_v_746_, lean_object* v_k_747_, lean_object* v_as_748_, lean_object* v_k_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_744_, v_keys_745_, v_v_746_, v_k_747_, v_as_748_, v_k_749_, v_x_750_, v_x_751_);
lean_dec_ref(v_k_749_);
lean_dec_ref(v_keys_745_);
lean_dec(v_x_744_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_x_753_, lean_object* v_keys_754_, lean_object* v_v_755_, lean_object* v_k_756_, lean_object* v_as_757_, lean_object* v_k_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_x_753_, v_keys_754_, v_v_755_, v_k_756_, v_as_757_, v_k_758_);
lean_dec_ref(v_k_758_);
lean_dec_ref(v_keys_754_);
lean_dec(v_x_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v_keys_760_, lean_object* v_v_761_, lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_760_, v_v_761_, v___x_763_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
else
{
lean_object* v_val_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v_val_766_ = lean_ctor_get(v_x_762_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_762_);
if (v_isSharedCheck_775_ == 0)
{
v___x_768_ = v_x_762_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_val_766_);
lean_dec(v_x_762_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_760_, v_v_761_, v___x_770_, v_val_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v_keys_776_, lean_object* v_v_777_, lean_object* v_x_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_776_, v_v_777_, v_x_778_);
lean_dec_ref(v_keys_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_keys_780_, lean_object* v_v_781_, lean_object* v_x_782_, size_t v_x_783_, size_t v_x_784_, lean_object* v_x_785_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v_es_786_; size_t v___x_787_; size_t v___x_788_; lean_object* v_j_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_es_786_ = lean_ctor_get(v_x_782_, 0);
v___x_787_ = ((size_t)31ULL);
v___x_788_ = lean_usize_land(v_x_783_, v___x_787_);
v_j_789_ = lean_usize_to_nat(v___x_788_);
v___x_790_ = lean_array_get_size(v_es_786_);
v___x_791_ = lean_nat_dec_lt(v_j_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_dec(v_j_789_);
lean_dec(v_x_785_);
lean_dec_ref(v_v_781_);
return v_x_782_;
}
else
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_859_; 
lean_inc_ref(v_es_786_);
v_isSharedCheck_859_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v_x_782_, 0);
lean_dec(v_unused_860_);
v___x_793_ = v_x_782_;
v_isShared_794_ = v_isSharedCheck_859_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_x_782_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_859_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_v_795_; lean_object* v___x_796_; lean_object* v_xs_x27_797_; lean_object* v___y_799_; 
v_v_795_ = lean_array_fget(v_es_786_, v_j_789_);
v___x_796_ = lean_box(0);
v_xs_x27_797_ = lean_array_fset(v_es_786_, v_j_789_, v___x_796_);
switch(lean_obj_tag(v_v_795_))
{
case 0:
{
lean_object* v_key_804_; lean_object* v_val_805_; uint8_t v___x_806_; 
v_key_804_ = lean_ctor_get(v_v_795_, 0);
v_val_805_ = lean_ctor_get(v_v_795_, 1);
v___x_806_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_785_, v_key_804_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_box(0);
v___x_808_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_780_, v_v_781_, v___x_807_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_dec(v_x_785_);
v___y_799_ = v_v_795_;
goto v___jp_798_;
}
else
{
lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
lean_inc(v_val_805_);
lean_inc(v_key_804_);
lean_dec_ref_known(v_v_795_, 2);
v_val_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_817_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_804_, v_val_805_, v_x_785_, v_val_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
v___y_799_ = v___x_815_;
goto v___jp_798_;
}
}
}
}
else
{
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_828_; 
lean_inc(v_val_805_);
v_isSharedCheck_828_ = !lean_is_exclusive(v_v_795_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; lean_object* v_unused_830_; 
v_unused_829_ = lean_ctor_get(v_v_795_, 1);
lean_dec(v_unused_829_);
v_unused_830_ = lean_ctor_get(v_v_795_, 0);
lean_dec(v_unused_830_);
v___x_819_ = v_v_795_;
v_isShared_820_ = v_isSharedCheck_828_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_v_795_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_828_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_val_805_);
v___x_822_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_780_, v_v_781_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; 
lean_del_object(v___x_819_);
lean_dec(v_x_785_);
v___x_823_ = lean_box(2);
v___y_799_ = v___x_823_;
goto v___jp_798_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; 
v_val_824_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v___x_822_, 1);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_val_824_);
lean_ctor_set(v___x_819_, 0, v_x_785_);
v___x_826_ = v___x_819_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_x_785_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v___y_799_ = v___x_826_;
goto v___jp_798_;
}
}
}
}
}
case 1:
{
lean_object* v_node_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_854_; 
v_node_831_ = lean_ctor_get(v_v_795_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_v_795_);
if (v_isSharedCheck_854_ == 0)
{
v___x_833_ = v_v_795_;
v_isShared_834_ = v_isSharedCheck_854_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_node_831_);
lean_dec(v_v_795_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_854_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
size_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; lean_object* v_newNode_839_; lean_object* v___x_840_; 
v___x_835_ = ((size_t)5ULL);
v___x_836_ = lean_usize_shift_right(v_x_783_, v___x_835_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_x_784_, v___x_837_);
v_newNode_839_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_780_, v_v_781_, v_node_831_, v___x_836_, v___x_838_, v_x_785_);
lean_inc_ref(v_newNode_839_);
v___x_840_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_842_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v_newNode_839_);
v___x_842_ = v___x_833_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_newNode_839_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
v___y_799_ = v___x_842_;
goto v___jp_798_;
}
}
else
{
lean_object* v_val_844_; lean_object* v_fst_845_; lean_object* v_snd_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v_newNode_839_);
lean_del_object(v___x_833_);
v_val_844_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_844_);
lean_dec_ref_known(v___x_840_, 1);
v_fst_845_ = lean_ctor_get(v_val_844_, 0);
v_snd_846_ = lean_ctor_get(v_val_844_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v_val_844_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v_val_844_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_snd_846_);
lean_inc(v_fst_845_);
lean_dec(v_val_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_fst_845_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_snd_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v___y_799_ = v___x_851_;
goto v___jp_798_;
}
}
}
}
}
default: 
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_box(0);
v___x_856_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_780_, v_v_781_, v___x_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_dec(v_x_785_);
v___y_799_ = v_v_795_;
goto v___jp_798_;
}
else
{
lean_object* v_val_857_; lean_object* v___x_858_; 
v_val_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_x_785_);
lean_ctor_set(v___x_858_, 1, v_val_857_);
v___y_799_ = v___x_858_;
goto v___jp_798_;
}
}
}
v___jp_798_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_array_fset(v_xs_x27_797_, v_j_789_, v___y_799_);
lean_dec(v_j_789_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_800_);
v___x_802_ = v___x_793_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
else
{
lean_object* v_ks_861_; lean_object* v_vs_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_895_; 
v_ks_861_ = lean_ctor_get(v_x_782_, 0);
v_vs_862_ = lean_ctor_get(v_x_782_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_782_);
if (v_isSharedCheck_895_ == 0)
{
v___x_864_ = v_x_782_;
v_isShared_865_ = v_isSharedCheck_895_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_vs_862_);
lean_inc(v_ks_861_);
lean_dec(v_x_782_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_895_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; 
v___x_866_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__4(v_ks_861_, v_x_785_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_868_; 
if (v_isShared_865_ == 0)
{
v___x_868_ = v___x_864_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_ks_861_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_vs_862_);
v___x_868_ = v_reuseFailAlloc_873_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_box(0);
v___x_870_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_780_, v_v_781_, v___x_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_dec(v_x_785_);
return v___x_868_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_872_; 
v_val_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_val_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v___x_868_, v_x_783_, v_x_784_, v_x_785_, v_val_871_);
return v___x_872_;
}
}
}
else
{
lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_894_; 
v_val_874_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_894_ == 0)
{
v___x_876_ = v___x_866_;
v_isShared_877_ = v_isSharedCheck_894_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_dec(v___x_866_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_894_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_v_x27_878_; lean_object* v_keys_879_; lean_object* v_vals_880_; lean_object* v___x_882_; 
v_v_x27_878_ = lean_array_fget(v_vs_862_, v_val_874_);
lean_inc(v_val_874_);
v_keys_879_ = l_Array_eraseIdx___redArg(v_ks_861_, v_val_874_);
v_vals_880_ = l_Array_eraseIdx___redArg(v_vs_862_, v_val_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v_v_x27_878_);
v___x_882_ = v___x_876_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_v_x27_878_);
v___x_882_ = v_reuseFailAlloc_893_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_780_, v_v_781_, v___x_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_885_; 
lean_dec(v_x_785_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v_vals_880_);
lean_ctor_set(v___x_864_, 0, v_keys_879_);
v___x_885_ = v___x_864_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_keys_879_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_vals_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v_val_887_; lean_object* v_keys_888_; lean_object* v_vals_889_; lean_object* v___x_891_; 
v_val_887_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v___x_883_, 1);
v_keys_888_ = lean_array_push(v_keys_879_, v_x_785_);
v_vals_889_ = lean_array_push(v_vals_880_, v_val_887_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v_vals_889_);
lean_ctor_set(v___x_864_, 0, v_keys_888_);
v___x_891_ = v___x_864_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_keys_888_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_vals_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_keys_896_, lean_object* v_v_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
size_t v_x_2467__boxed_902_; size_t v_x_2468__boxed_903_; lean_object* v_res_904_; 
v_x_2467__boxed_902_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_x_2468__boxed_903_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_904_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_896_, v_v_897_, v_x_898_, v_x_2467__boxed_902_, v_x_2468__boxed_903_, v_x_901_);
lean_dec_ref(v_keys_896_);
return v_res_904_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_msg_906_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0);
v___x_908_ = lean_panic_fn_borrowed(v___x_907_, v_msg_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_912_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2));
v___x_913_ = lean_unsigned_to_nat(23u);
v___x_914_ = lean_unsigned_to_nat(166u);
v___x_915_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1));
v___x_916_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0));
v___x_917_ = l_mkPanicMessageWithDecl(v___x_916_, v___x_915_, v___x_914_, v___x_913_, v___x_912_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(lean_object* v_d_918_, lean_object* v_keys_919_, lean_object* v_v_920_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_array_get_size(v_keys_919_);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_nat_dec_eq(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v_k_925_; uint64_t v___x_926_; size_t v_h_927_; size_t v___x_928_; lean_object* v___x_929_; 
v___x_924_ = lean_box(0);
v_k_925_ = lean_array_get_borrowed(v___x_924_, v_keys_919_, v___x_922_);
v___x_926_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_925_);
v_h_927_ = lean_uint64_to_usize(v___x_926_);
v___x_928_ = ((size_t)1ULL);
lean_inc(v_k_925_);
v___x_929_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_919_, v_v_920_, v_d_918_, v_h_927_, v___x_928_, v_k_925_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_v_920_);
lean_dec_ref(v_d_918_);
v___x_930_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3);
v___x_931_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v___x_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_932_, lean_object* v_keys_933_, lean_object* v_v_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_d_932_, v_keys_933_, v_v_934_);
lean_dec_ref(v_keys_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_936_, lean_object* v_thm_937_){
_start:
{
lean_object* v_tree_938_; lean_object* v_erased_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_950_; 
v_tree_938_ = lean_ctor_get(v_x_936_, 0);
v_erased_939_ = lean_ctor_get(v_x_936_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_941_ = v_x_936_;
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_erased_939_);
lean_inc(v_tree_938_);
lean_dec(v_x_936_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_declName_943_; lean_object* v_keys_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v_declName_943_ = lean_ctor_get(v_thm_937_, 0);
lean_inc(v_declName_943_);
v_keys_944_ = lean_ctor_get(v_thm_937_, 2);
lean_inc_ref(v_keys_944_);
v___x_945_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_tree_938_, v_keys_944_, v_thm_937_);
lean_dec_ref(v_keys_944_);
v___x_946_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_erased_939_, v_declName_943_);
lean_dec(v_declName_943_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_946_);
lean_ctor_set(v___x_941_, 0, v___x_945_);
v___x_948_ = v___x_941_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_945_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v___y_951_){
_start:
{
lean_inc_ref(v___y_951_);
return v___y_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v___y_952_);
lean_dec_ref(v___y_952_);
return v_res_953_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___f_966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___f_967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_968_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3);
v___f_969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___f_969_);
lean_ctor_set(v___x_971_, 2, v___x_968_);
lean_ctor_set(v___x_971_, 3, v___f_967_);
lean_ctor_set(v___x_971_, 4, v___f_966_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_);
v___x_974_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_978_, v_x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(v_00_u03b2_981_, v_x_982_, v_x_983_);
lean_dec(v_x_983_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, size_t v_x_987_, lean_object* v_x_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_986_, v_x_987_, v_x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
size_t v_x_2836__boxed_994_; lean_object* v_res_995_; 
v_x_2836__boxed_994_ = lean_unbox_usize(v_x_992_);
lean_dec(v_x_992_);
v_res_995_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_990_, v_x_991_, v_x_2836__boxed_994_, v_x_993_);
lean_dec(v_x_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(lean_object* v_00_u03b2_996_, lean_object* v_x_997_, size_t v_x_998_, size_t v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_x_997_, v_x_998_, v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
size_t v_x_2847__boxed_1009_; size_t v_x_2848__boxed_1010_; lean_object* v_res_1011_; 
v_x_2847__boxed_1009_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_x_2848__boxed_1010_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_res_1011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(v_00_u03b2_1003_, v_x_1004_, v_x_2847__boxed_1009_, v_x_2848__boxed_1010_, v_x_1007_, v_x_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_x_1012_, lean_object* v_keys_1013_, lean_object* v_v_1014_, lean_object* v_k_1015_, lean_object* v_as_1016_, lean_object* v_k_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___redArg(v_x_1012_, v_keys_1013_, v_v_1014_, v_k_1015_, v_as_1016_, v_k_1017_, v_x_1018_, v_x_1019_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_x_1023_, lean_object* v_keys_1024_, lean_object* v_v_1025_, lean_object* v_k_1026_, lean_object* v_as_1027_, lean_object* v_k_1028_, lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_x_1023_, v_keys_1024_, v_v_1025_, v_k_1026_, v_as_1027_, v_k_1028_, v_x_1029_, v_x_1030_, v_x_1031_, v_x_1032_);
lean_dec_ref(v_k_1028_);
lean_dec_ref(v_keys_1024_);
lean_dec(v_x_1023_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(lean_object* v_00_u03b2_1034_, lean_object* v_n_1035_, lean_object* v_k_1036_, lean_object* v_v_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___redArg(v_n_1035_, v_k_1036_, v_v_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_1039_, size_t v_depth_1040_, lean_object* v_keys_1041_, lean_object* v_vals_1042_, lean_object* v_heq_1043_, lean_object* v_i_1044_, lean_object* v_entries_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___redArg(v_depth_1040_, v_keys_1041_, v_vals_1042_, v_i_1044_, v_entries_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12___boxed(lean_object* v_00_u03b2_1047_, lean_object* v_depth_1048_, lean_object* v_keys_1049_, lean_object* v_vals_1050_, lean_object* v_heq_1051_, lean_object* v_i_1052_, lean_object* v_entries_1053_){
_start:
{
size_t v_depth_boxed_1054_; lean_object* v_res_1055_; 
v_depth_boxed_1054_ = lean_unbox_usize(v_depth_1048_);
lean_dec(v_depth_1048_);
v_res_1055_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__12(v_00_u03b2_1047_, v_depth_boxed_1054_, v_keys_1049_, v_vals_1050_, v_heq_1051_, v_i_1052_, v_entries_1053_);
lean_dec_ref(v_vals_1050_);
lean_dec_ref(v_keys_1049_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13(lean_object* v_00_u03b2_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11_spec__13___redArg(v_x_1057_, v_x_1058_, v_x_1059_, v_x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_getExtTheorems___lam__0(lean_object* v_x1_1062_, lean_object* v_x2_1063_){
_start:
{
lean_object* v_priority_1064_; lean_object* v_priority_1065_; uint8_t v___x_1066_; 
v_priority_1064_ = lean_ctor_get(v_x1_1062_, 1);
v_priority_1065_ = lean_ctor_get(v_x2_1063_, 1);
v___x_1066_ = lean_nat_dec_lt(v_priority_1064_, v_priority_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(lean_object* v_x1_1067_, lean_object* v_x2_1068_){
_start:
{
uint8_t v_res_1069_; lean_object* v_r_1070_; 
v_res_1069_ = l_Lean_Meta_Ext_getExtTheorems___lam__0(v_x1_1067_, v_x2_1068_);
lean_dec_ref(v_x2_1068_);
lean_dec_ref(v_x1_1067_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__1(lean_object* v___x_1071_, lean_object* v___x_1072_, lean_object* v___x_1073_, lean_object* v_x1_1074_, lean_object* v_x2_1075_){
_start:
{
lean_object* v_erased_1076_; lean_object* v_declName_1077_; uint8_t v___x_1078_; 
v_erased_1076_ = lean_ctor_get(v___x_1071_, 1);
lean_inc_ref(v_erased_1076_);
lean_dec_ref(v___x_1071_);
v_declName_1077_ = lean_ctor_get(v_x2_1075_, 0);
lean_inc(v_declName_1077_);
v___x_1078_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1072_, v___x_1073_, v_erased_1076_, v_declName_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_array_push(v_x1_1074_, v_x2_1075_);
return v___x_1079_;
}
else
{
lean_dec_ref(v_x2_1075_);
return v_x1_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object* v_ty_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_env_1109_; lean_object* v___x_1110_; lean_object* v_ext_1111_; lean_object* v_toEnvExtension_1112_; lean_object* v_asyncMode_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_tree_1116_; lean_object* v___x_1117_; 
v___x_1108_ = lean_st_ref_get(v_a_1106_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1109_);
lean_dec(v___x_1108_);
v___x_1110_ = l_Lean_Meta_Ext_extExtension;
v_ext_1111_ = lean_ctor_get(v___x_1110_, 1);
v_toEnvExtension_1112_ = lean_ctor_get(v_ext_1111_, 0);
v_asyncMode_1113_ = lean_ctor_get(v_toEnvExtension_1112_, 2);
v___x_1114_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1115_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1114_, v___x_1110_, v_env_1109_, v_asyncMode_1113_);
v_tree_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_tree_1116_);
v___x_1117_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_tree_1116_, v_ty_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec_ref(v_tree_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1147_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1147_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1147_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___f_1122_; lean_object* v___y_1124_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___f_1122_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__0));
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_array_get_size(v_a_1118_);
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_1135_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__10));
v___x_1136_ = lean_nat_dec_lt(v___x_1132_, v___x_1133_);
if (v___x_1136_ == 0)
{
lean_dec(v_a_1118_);
lean_dec(v___x_1115_);
v___y_1124_ = v___x_1134_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___f_1139_; uint8_t v___x_1140_; 
v___x_1137_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__11));
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__12));
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_getExtTheorems___lam__1), 5, 3);
lean_closure_set(v___f_1139_, 0, v___x_1115_);
lean_closure_set(v___f_1139_, 1, v___x_1137_);
lean_closure_set(v___f_1139_, 2, v___x_1138_);
v___x_1140_ = lean_nat_dec_le(v___x_1133_, v___x_1133_);
if (v___x_1140_ == 0)
{
if (v___x_1136_ == 0)
{
lean_dec_ref(v___f_1139_);
lean_dec(v_a_1118_);
v___y_1124_ = v___x_1134_;
goto v___jp_1123_;
}
else
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1133_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1135_, v___f_1139_, v_a_1118_, v___x_1141_, v___x_1142_, v___x_1134_);
v___y_1124_ = v___x_1143_;
goto v___jp_1123_;
}
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_of_nat(v___x_1133_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1135_, v___f_1139_, v_a_1118_, v___x_1144_, v___x_1145_, v___x_1134_);
v___y_1124_ = v___x_1146_;
goto v___jp_1123_;
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_array_get_size(v___y_1124_);
v___x_1127_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(lean_box(0), v___f_1122_, v___y_1124_, v___x_1125_, v___x_1126_);
v___x_1128_ = l_Array_reverse___redArg(v___x_1127_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1128_);
v___x_1130_ = v___x_1120_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_dec(v___x_1115_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___boxed(lean_object* v_ty_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Meta_Ext_getExtTheorems(v_ty_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v_ks_1159_; lean_object* v_vs_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1184_; 
v_ks_1159_ = lean_ctor_get(v_x_1155_, 0);
v_vs_1160_ = lean_ctor_get(v_x_1155_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_x_1155_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1162_ = v_x_1155_;
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_vs_1160_);
lean_inc(v_ks_1159_);
lean_dec(v_x_1155_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_array_get_size(v_ks_1159_);
v___x_1165_ = lean_nat_dec_lt(v_x_1156_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
lean_dec(v_x_1156_);
v___x_1166_ = lean_array_push(v_ks_1159_, v_x_1157_);
v___x_1167_ = lean_array_push(v_vs_1160_, v_x_1158_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1167_);
lean_ctor_set(v___x_1162_, 0, v___x_1166_);
v___x_1169_ = v___x_1162_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
else
{
lean_object* v_k_x27_1171_; uint8_t v___x_1172_; 
v_k_x27_1171_ = lean_array_fget_borrowed(v_ks_1159_, v_x_1156_);
v___x_1172_ = lean_name_eq(v_x_1157_, v_k_x27_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1174_; 
if (v_isShared_1163_ == 0)
{
v___x_1174_ = v___x_1162_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_ks_1159_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_vs_1160_);
v___x_1174_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_unsigned_to_nat(1u);
v___x_1176_ = lean_nat_add(v_x_1156_, v___x_1175_);
lean_dec(v_x_1156_);
v_x_1155_ = v___x_1174_;
v_x_1156_ = v___x_1176_;
goto _start;
}
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1179_ = lean_array_fset(v_ks_1159_, v_x_1156_, v_x_1157_);
v___x_1180_ = lean_array_fset(v_vs_1160_, v_x_1156_, v_x_1158_);
lean_dec(v_x_1156_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1180_);
lean_ctor_set(v___x_1162_, 0, v___x_1179_);
v___x_1182_ = v___x_1162_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1185_, lean_object* v_k_1186_, lean_object* v_v_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1185_, v___x_1188_, v_k_1186_, v_v_1187_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(lean_object* v_x_1191_, size_t v_x_1192_, size_t v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_es_1196_; size_t v___x_1197_; size_t v___x_1198_; lean_object* v_j_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_es_1196_ = lean_ctor_get(v_x_1191_, 0);
v___x_1197_ = ((size_t)31ULL);
v___x_1198_ = lean_usize_land(v_x_1192_, v___x_1197_);
v_j_1199_ = lean_usize_to_nat(v___x_1198_);
v___x_1200_ = lean_array_get_size(v_es_1196_);
v___x_1201_ = lean_nat_dec_lt(v_j_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_dec(v_j_1199_);
lean_dec(v_x_1195_);
lean_dec(v_x_1194_);
return v_x_1191_;
}
else
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1240_; 
lean_inc_ref(v_es_1196_);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v_x_1191_, 0);
lean_dec(v_unused_1241_);
v___x_1203_ = v_x_1191_;
v_isShared_1204_ = v_isSharedCheck_1240_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v_x_1191_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1240_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_v_1205_; lean_object* v___x_1206_; lean_object* v_xs_x27_1207_; lean_object* v___y_1209_; 
v_v_1205_ = lean_array_fget(v_es_1196_, v_j_1199_);
v___x_1206_ = lean_box(0);
v_xs_x27_1207_ = lean_array_fset(v_es_1196_, v_j_1199_, v___x_1206_);
switch(lean_obj_tag(v_v_1205_))
{
case 0:
{
lean_object* v_key_1214_; lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
v_key_1214_ = lean_ctor_get(v_v_1205_, 0);
v_val_1215_ = lean_ctor_get(v_v_1205_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_v_1205_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1217_ = v_v_1205_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_inc(v_key_1214_);
lean_dec(v_v_1205_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_name_eq(v_x_1194_, v_key_1214_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1217_);
v___x_1220_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1214_, v_val_1215_, v_x_1194_, v_x_1195_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
v___y_1209_ = v___x_1221_;
goto v___jp_1208_;
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_val_1215_);
lean_dec(v_key_1214_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_x_1195_);
lean_ctor_set(v___x_1217_, 0, v_x_1194_);
v___x_1223_ = v___x_1217_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_x_1194_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_x_1195_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
v___y_1209_ = v___x_1223_;
goto v___jp_1208_;
}
}
}
}
case 1:
{
lean_object* v_node_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1238_; 
v_node_1226_ = lean_ctor_get(v_v_1205_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_v_1205_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1228_ = v_v_1205_;
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_node_1226_);
lean_dec(v_v_1205_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1230_ = ((size_t)5ULL);
v___x_1231_ = lean_usize_shift_right(v_x_1192_, v___x_1230_);
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_x_1193_, v___x_1232_);
v___x_1234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_node_1226_, v___x_1231_, v___x_1233_, v_x_1194_, v_x_1195_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1234_);
v___x_1236_ = v___x_1228_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
v___y_1209_ = v___x_1236_;
goto v___jp_1208_;
}
}
}
default: 
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_x_1194_);
lean_ctor_set(v___x_1239_, 1, v_x_1195_);
v___y_1209_ = v___x_1239_;
goto v___jp_1208_;
}
}
v___jp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_array_fset(v_xs_x27_1207_, v_j_1199_, v___y_1209_);
lean_dec(v_j_1199_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1210_);
v___x_1212_ = v___x_1203_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
else
{
lean_object* v_ks_1242_; lean_object* v_vs_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1263_; 
v_ks_1242_ = lean_ctor_get(v_x_1191_, 0);
v_vs_1243_ = lean_ctor_get(v_x_1191_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1245_ = v_x_1191_;
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_vs_1243_);
lean_inc(v_ks_1242_);
lean_dec(v_x_1191_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_ks_1242_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_vs_1243_);
v___x_1248_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v_newNode_1249_; uint8_t v___y_1251_; size_t v___x_1257_; uint8_t v___x_1258_; 
v_newNode_1249_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v___x_1248_, v_x_1194_, v_x_1195_);
v___x_1257_ = ((size_t)7ULL);
v___x_1258_ = lean_usize_dec_le(v___x_1257_, v_x_1193_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1249_);
v___x_1260_ = lean_unsigned_to_nat(4u);
v___x_1261_ = lean_nat_dec_lt(v___x_1259_, v___x_1260_);
lean_dec(v___x_1259_);
v___y_1251_ = v___x_1261_;
goto v___jp_1250_;
}
else
{
v___y_1251_ = v___x_1258_;
goto v___jp_1250_;
}
v___jp_1250_:
{
if (v___y_1251_ == 0)
{
lean_object* v_ks_1252_; lean_object* v_vs_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_ks_1252_ = lean_ctor_get(v_newNode_1249_, 0);
lean_inc_ref(v_ks_1252_);
v_vs_1253_ = lean_ctor_get(v_newNode_1249_, 1);
lean_inc_ref(v_vs_1253_);
lean_dec_ref(v_newNode_1249_);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0);
v___x_1256_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_x_1193_, v_ks_1252_, v_vs_1253_, v___x_1254_, v___x_1255_);
lean_dec_ref(v_vs_1253_);
lean_dec_ref(v_ks_1252_);
return v___x_1256_;
}
else
{
return v_newNode_1249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_1264_, lean_object* v_keys_1265_, lean_object* v_vals_1266_, lean_object* v_i_1267_, lean_object* v_entries_1268_){
_start:
{
lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = lean_array_get_size(v_keys_1265_);
v___x_1270_ = lean_nat_dec_lt(v_i_1267_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec(v_i_1267_);
return v_entries_1268_;
}
else
{
lean_object* v_k_1271_; lean_object* v_v_1272_; uint64_t v___y_1274_; 
v_k_1271_ = lean_array_fget_borrowed(v_keys_1265_, v_i_1267_);
v_v_1272_ = lean_array_fget_borrowed(v_vals_1266_, v_i_1267_);
if (lean_obj_tag(v_k_1271_) == 0)
{
uint64_t v___x_1285_; 
v___x_1285_ = 1723ULL;
v___y_1274_ = v___x_1285_;
goto v___jp_1273_;
}
else
{
uint64_t v_hash_1286_; 
v_hash_1286_ = lean_ctor_get_uint64(v_k_1271_, sizeof(void*)*2);
v___y_1274_ = v_hash_1286_;
goto v___jp_1273_;
}
v___jp_1273_:
{
size_t v_h_1275_; size_t v___x_1276_; lean_object* v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v_h_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_h_1275_ = lean_uint64_to_usize(v___y_1274_);
v___x_1276_ = ((size_t)5ULL);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_sub(v_depth_1264_, v___x_1278_);
v___x_1280_ = lean_usize_mul(v___x_1276_, v___x_1279_);
v_h_1281_ = lean_usize_shift_right(v_h_1275_, v___x_1280_);
v___x_1282_ = lean_nat_add(v_i_1267_, v___x_1277_);
lean_dec(v_i_1267_);
lean_inc(v_v_1272_);
lean_inc(v_k_1271_);
v___x_1283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_entries_1268_, v_h_1281_, v_depth_1264_, v_k_1271_, v_v_1272_);
v_i_1267_ = v___x_1282_;
v_entries_1268_ = v___x_1283_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1287_, lean_object* v_keys_1288_, lean_object* v_vals_1289_, lean_object* v_i_1290_, lean_object* v_entries_1291_){
_start:
{
size_t v_depth_boxed_1292_; lean_object* v_res_1293_; 
v_depth_boxed_1292_ = lean_unbox_usize(v_depth_1287_);
lean_dec(v_depth_1287_);
v_res_1293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1292_, v_keys_1288_, v_vals_1289_, v_i_1290_, v_entries_1291_);
lean_dec_ref(v_vals_1289_);
lean_dec_ref(v_keys_1288_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
size_t v_x_358__boxed_1299_; size_t v_x_359__boxed_1300_; lean_object* v_res_1301_; 
v_x_358__boxed_1299_ = lean_unbox_usize(v_x_1295_);
lean_dec(v_x_1295_);
v_x_359__boxed_1300_ = lean_unbox_usize(v_x_1296_);
lean_dec(v_x_1296_);
v_res_1301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1294_, v_x_358__boxed_1299_, v_x_359__boxed_1300_, v_x_1297_, v_x_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(lean_object* v_x_1302_, lean_object* v_x_1303_, lean_object* v_x_1304_){
_start:
{
uint64_t v___y_1306_; 
if (lean_obj_tag(v_x_1303_) == 0)
{
uint64_t v___x_1310_; 
v___x_1310_ = 1723ULL;
v___y_1306_ = v___x_1310_;
goto v___jp_1305_;
}
else
{
uint64_t v_hash_1311_; 
v_hash_1311_ = lean_ctor_get_uint64(v_x_1303_, sizeof(void*)*2);
v___y_1306_ = v_hash_1311_;
goto v___jp_1305_;
}
v___jp_1305_:
{
size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_uint64_to_usize(v___y_1306_);
v___x_1308_ = ((size_t)1ULL);
v___x_1309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1302_, v___x_1307_, v___x_1308_, v_x_1303_, v_x_1304_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object* v_d_1312_, lean_object* v_declName_1313_){
_start:
{
lean_object* v_tree_1314_; lean_object* v_erased_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1324_; 
v_tree_1314_ = lean_ctor_get(v_d_1312_, 0);
v_erased_1315_ = lean_ctor_get(v_d_1312_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_d_1312_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1317_ = v_d_1312_;
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_erased_1315_);
lean_inc(v_tree_1314_);
lean_dec(v_d_1312_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_erased_1315_, v_declName_1313_, v___x_1319_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___x_1320_);
v___x_1322_ = v___x_1317_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_tree_1314_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0(lean_object* v_00_u03b2_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_x_1326_, v_x_1327_, v_x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(lean_object* v_00_u03b2_1330_, lean_object* v_x_1331_, size_t v_x_1332_, size_t v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1331_, v_x_1332_, v_x_1333_, v_x_1334_, v_x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_){
_start:
{
size_t v_x_560__boxed_1343_; size_t v_x_561__boxed_1344_; lean_object* v_res_1345_; 
v_x_560__boxed_1343_ = lean_unbox_usize(v_x_1339_);
lean_dec(v_x_1339_);
v_x_561__boxed_1344_ = lean_unbox_usize(v_x_1340_);
lean_dec(v_x_1340_);
v_res_1345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(v_00_u03b2_1337_, v_x_1338_, v_x_560__boxed_1343_, v_x_561__boxed_1344_, v_x_1341_, v_x_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1346_, lean_object* v_n_1347_, lean_object* v_k_1348_, lean_object* v_v_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v_n_1347_, v_k_1348_, v_v_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1351_, size_t v_depth_1352_, lean_object* v_keys_1353_, lean_object* v_vals_1354_, lean_object* v_heq_1355_, lean_object* v_i_1356_, lean_object* v_entries_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_1352_, v_keys_1353_, v_vals_1354_, v_i_1356_, v_entries_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1359_, lean_object* v_depth_1360_, lean_object* v_keys_1361_, lean_object* v_vals_1362_, lean_object* v_heq_1363_, lean_object* v_i_1364_, lean_object* v_entries_1365_){
_start:
{
size_t v_depth_boxed_1366_; lean_object* v_res_1367_; 
v_depth_boxed_1366_ = lean_unbox_usize(v_depth_1360_);
lean_dec(v_depth_1360_);
v_res_1367_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(v_00_u03b2_1359_, v_depth_boxed_1366_, v_keys_1361_, v_vals_1362_, v_heq_1363_, v_i_1364_, v_entries_1365_);
lean_dec_ref(v_vals_1362_);
lean_dec_ref(v_keys_1361_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1369_, v_x_1370_, v_x_1371_, v_x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(lean_object* v_declName_1374_, uint8_t v_x1_1375_, lean_object* v_x2_1376_){
_start:
{
if (v_x1_1375_ == 0)
{
lean_object* v_declName_1377_; uint8_t v___x_1378_; 
v_declName_1377_ = lean_ctor_get(v_x2_1376_, 0);
v___x_1378_ = lean_name_eq(v_declName_1377_, v_declName_1374_);
return v___x_1378_;
}
else
{
return v_x1_1375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(lean_object* v_declName_1379_, lean_object* v_x1_1380_, lean_object* v_x2_1381_){
_start:
{
uint8_t v_x1_1194__boxed_1382_; uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_x1_1194__boxed_1382_ = lean_unbox(v_x1_1380_);
v_res_1383_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(v_declName_1379_, v_x1_1194__boxed_1382_, v_x2_1381_);
lean_dec_ref(v_x2_1381_);
lean_dec(v_declName_1379_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(lean_object* v_f_1385_, lean_object* v_as_1386_, size_t v_i_1387_, size_t v_stop_1388_, lean_object* v_b_1389_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_eq(v_i_1387_, v_stop_1388_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; 
v___x_1391_ = lean_array_uget_borrowed(v_as_1386_, v_i_1387_);
lean_inc(v_f_1385_);
lean_inc(v___x_1391_);
v___x_1392_ = lean_apply_2(v_f_1385_, v_b_1389_, v___x_1391_);
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_add(v_i_1387_, v___x_1393_);
v_i_1387_ = v___x_1394_;
v_b_1389_ = v___x_1392_;
goto _start;
}
else
{
lean_dec(v_f_1385_);
return v_b_1389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg___boxed(lean_object* v_f_1396_, lean_object* v_as_1397_, lean_object* v_i_1398_, lean_object* v_stop_1399_, lean_object* v_b_1400_){
_start:
{
size_t v_i_boxed_1401_; size_t v_stop_boxed_1402_; lean_object* v_res_1403_; 
v_i_boxed_1401_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_stop_boxed_1402_ = lean_unbox_usize(v_stop_1399_);
lean_dec(v_stop_1399_);
v_res_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1396_, v_as_1397_, v_i_boxed_1401_, v_stop_boxed_1402_, v_b_1400_);
lean_dec_ref(v_as_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(lean_object* v_f_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v_vs_1407_; lean_object* v_children_1408_; lean_object* v___x_1409_; lean_object* v_s_1411_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_vs_1407_ = lean_ctor_get(v_x_1406_, 0);
v_children_1408_ = lean_ctor_get(v_x_1406_, 1);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_array_get_size(v_vs_1407_);
v___x_1422_ = lean_nat_dec_lt(v___x_1409_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_array_get_size(v_children_1408_);
v___x_1424_ = lean_nat_dec_lt(v___x_1409_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_dec(v_f_1404_);
return v_x_1405_;
}
else
{
uint8_t v___x_1425_; 
v___x_1425_ = lean_nat_dec_le(v___x_1423_, v___x_1423_);
if (v___x_1425_ == 0)
{
if (v___x_1424_ == 0)
{
lean_dec(v_f_1404_);
return v_x_1405_;
}
else
{
size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1423_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1404_, v_children_1408_, v___x_1426_, v___x_1427_, v_x_1405_);
return v___x_1428_;
}
}
else
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = lean_usize_of_nat(v___x_1423_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1404_, v_children_1408_, v___x_1429_, v___x_1430_, v_x_1405_);
return v___x_1431_;
}
}
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_nat_dec_le(v___x_1421_, v___x_1421_);
if (v___x_1432_ == 0)
{
if (v___x_1422_ == 0)
{
v_s_1411_ = v_x_1405_;
goto v___jp_1410_;
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1421_);
lean_inc(v_f_1404_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1404_, v_vs_1407_, v___x_1433_, v___x_1434_, v_x_1405_);
v_s_1411_ = v___x_1435_;
goto v___jp_1410_;
}
}
else
{
size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = lean_usize_of_nat(v___x_1421_);
lean_inc(v_f_1404_);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1404_, v_vs_1407_, v___x_1436_, v___x_1437_, v_x_1405_);
v_s_1411_ = v___x_1438_;
goto v___jp_1410_;
}
}
v___jp_1410_:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = lean_array_get_size(v_children_1408_);
v___x_1413_ = lean_nat_dec_lt(v___x_1409_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v_f_1404_);
return v_s_1411_;
}
else
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_nat_dec_le(v___x_1412_, v___x_1412_);
if (v___x_1414_ == 0)
{
if (v___x_1413_ == 0)
{
lean_dec(v_f_1404_);
return v_s_1411_;
}
else
{
size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = ((size_t)0ULL);
v___x_1416_ = lean_usize_of_nat(v___x_1412_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1404_, v_children_1408_, v___x_1415_, v___x_1416_, v_s_1411_);
return v___x_1417_;
}
}
else
{
size_t v___x_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = lean_usize_of_nat(v___x_1412_);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1404_, v_children_1408_, v___x_1418_, v___x_1419_, v_s_1411_);
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(lean_object* v_f_1439_, lean_object* v_as_1440_, size_t v_i_1441_, size_t v_stop_1442_, lean_object* v_b_1443_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_eq(v_i_1441_, v_stop_1442_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v_snd_1446_; lean_object* v___x_1447_; size_t v___x_1448_; size_t v___x_1449_; 
v___x_1445_ = lean_array_uget_borrowed(v_as_1440_, v_i_1441_);
v_snd_1446_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_f_1439_);
v___x_1447_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1439_, v_b_1443_, v_snd_1446_);
v___x_1448_ = ((size_t)1ULL);
v___x_1449_ = lean_usize_add(v_i_1441_, v___x_1448_);
v_i_1441_ = v___x_1449_;
v_b_1443_ = v___x_1447_;
goto _start;
}
else
{
lean_dec(v_f_1439_);
return v_b_1443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_f_1451_, lean_object* v_as_1452_, lean_object* v_i_1453_, lean_object* v_stop_1454_, lean_object* v_b_1455_){
_start:
{
size_t v_i_boxed_1456_; size_t v_stop_boxed_1457_; lean_object* v_res_1458_; 
v_i_boxed_1456_ = lean_unbox_usize(v_i_1453_);
lean_dec(v_i_1453_);
v_stop_boxed_1457_ = lean_unbox_usize(v_stop_1454_);
lean_dec(v_stop_1454_);
v_res_1458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1451_, v_as_1452_, v_i_boxed_1456_, v_stop_boxed_1457_, v_b_1455_);
lean_dec_ref(v_as_1452_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg___boxed(lean_object* v_f_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1459_, v_x_1460_, v_x_1461_);
lean_dec_ref(v_x_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(lean_object* v___f_1463_, uint8_t v_s_1464_, lean_object* v_x_1465_, lean_object* v_t_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_box(v_s_1464_);
v___x_1468_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v___f_1463_, v___x_1467_, v_t_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed(lean_object* v___f_1469_, lean_object* v_s_1470_, lean_object* v_x_1471_, lean_object* v_t_1472_){
_start:
{
uint8_t v_s_boxed_1473_; lean_object* v_res_1474_; 
v_s_boxed_1473_ = lean_unbox(v_s_1470_);
v_res_1474_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(v___f_1469_, v_s_boxed_1473_, v_x_1471_, v_t_1472_);
lean_dec_ref(v_t_1472_);
lean_dec(v_x_1471_);
return v_res_1474_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(lean_object* v_keys_1475_, lean_object* v_i_1476_, lean_object* v_k_1477_){
_start:
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_array_get_size(v_keys_1475_);
v___x_1479_ = lean_nat_dec_lt(v_i_1476_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec(v_i_1476_);
return v___x_1479_;
}
else
{
lean_object* v_k_x27_1480_; uint8_t v___x_1481_; 
v_k_x27_1480_ = lean_array_fget_borrowed(v_keys_1475_, v_i_1476_);
v___x_1481_ = lean_name_eq(v_k_1477_, v_k_x27_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_unsigned_to_nat(1u);
v___x_1483_ = lean_nat_add(v_i_1476_, v___x_1482_);
lean_dec(v_i_1476_);
v_i_1476_ = v___x_1483_;
goto _start;
}
else
{
lean_dec(v_i_1476_);
return v___x_1481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1485_, lean_object* v_i_1486_, lean_object* v_k_1487_){
_start:
{
uint8_t v_res_1488_; lean_object* v_r_1489_; 
v_res_1488_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1485_, v_i_1486_, v_k_1487_);
lean_dec(v_k_1487_);
lean_dec_ref(v_keys_1485_);
v_r_1489_ = lean_box(v_res_1488_);
return v_r_1489_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(lean_object* v_x_1490_, size_t v_x_1491_, lean_object* v_x_1492_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
lean_object* v_es_1493_; lean_object* v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; lean_object* v_j_1497_; lean_object* v___x_1498_; 
v_es_1493_ = lean_ctor_get(v_x_1490_, 0);
v___x_1494_ = lean_box(2);
v___x_1495_ = ((size_t)31ULL);
v___x_1496_ = lean_usize_land(v_x_1491_, v___x_1495_);
v_j_1497_ = lean_usize_to_nat(v___x_1496_);
v___x_1498_ = lean_array_get_borrowed(v___x_1494_, v_es_1493_, v_j_1497_);
lean_dec(v_j_1497_);
switch(lean_obj_tag(v___x_1498_))
{
case 0:
{
lean_object* v_key_1499_; uint8_t v___x_1500_; 
v_key_1499_ = lean_ctor_get(v___x_1498_, 0);
v___x_1500_ = lean_name_eq(v_x_1492_, v_key_1499_);
return v___x_1500_;
}
case 1:
{
lean_object* v_node_1501_; size_t v___x_1502_; size_t v___x_1503_; 
v_node_1501_ = lean_ctor_get(v___x_1498_, 0);
v___x_1502_ = ((size_t)5ULL);
v___x_1503_ = lean_usize_shift_right(v_x_1491_, v___x_1502_);
v_x_1490_ = v_node_1501_;
v_x_1491_ = v___x_1503_;
goto _start;
}
default: 
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
}
else
{
lean_object* v_ks_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_ks_1506_ = lean_ctor_get(v_x_1490_, 0);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_ks_1506_, v___x_1507_, v_x_1492_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
size_t v_x_1320__boxed_1512_; uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_x_1320__boxed_1512_ = lean_unbox_usize(v_x_1510_);
lean_dec(v_x_1510_);
v_res_1513_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1509_, v_x_1320__boxed_1512_, v_x_1511_);
lean_dec(v_x_1511_);
lean_dec_ref(v_x_1509_);
v_r_1514_ = lean_box(v_res_1513_);
return v_r_1514_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
uint64_t v___y_1518_; 
if (lean_obj_tag(v_x_1516_) == 0)
{
uint64_t v___x_1521_; 
v___x_1521_ = 1723ULL;
v___y_1518_ = v___x_1521_;
goto v___jp_1517_;
}
else
{
uint64_t v_hash_1522_; 
v_hash_1522_ = lean_ctor_get_uint64(v_x_1516_, sizeof(void*)*2);
v___y_1518_ = v_hash_1522_;
goto v___jp_1517_;
}
v___jp_1517_:
{
size_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = lean_uint64_to_usize(v___y_1518_);
v___x_1520_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1515_, v___x_1519_, v_x_1516_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
uint8_t v_res_1525_; lean_object* v_r_1526_; 
v_res_1525_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1523_, v_x_1524_);
lean_dec(v_x_1524_);
lean_dec_ref(v_x_1523_);
v_r_1526_ = lean_box(v_res_1525_);
return v_r_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(lean_object* v_f_1527_, lean_object* v_keys_1528_, lean_object* v_vals_1529_, lean_object* v_i_1530_, lean_object* v_acc_1531_){
_start:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = lean_array_get_size(v_keys_1528_);
v___x_1533_ = lean_nat_dec_lt(v_i_1530_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_dec(v_i_1530_);
lean_dec(v_f_1527_);
return v_acc_1531_;
}
else
{
lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_k_1534_ = lean_array_fget_borrowed(v_keys_1528_, v_i_1530_);
v_v_1535_ = lean_array_fget_borrowed(v_vals_1529_, v_i_1530_);
lean_inc(v_f_1527_);
lean_inc(v_v_1535_);
lean_inc(v_k_1534_);
v___x_1536_ = lean_apply_3(v_f_1527_, v_acc_1531_, v_k_1534_, v_v_1535_);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_add(v_i_1530_, v___x_1537_);
lean_dec(v_i_1530_);
v_i_1530_ = v___x_1538_;
v_acc_1531_ = v___x_1536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_1540_, lean_object* v_keys_1541_, lean_object* v_vals_1542_, lean_object* v_i_1543_, lean_object* v_acc_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1540_, v_keys_1541_, v_vals_1542_, v_i_1543_, v_acc_1544_);
lean_dec_ref(v_vals_1542_);
lean_dec_ref(v_keys_1541_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(lean_object* v_f_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
if (lean_obj_tag(v_x_1547_) == 0)
{
lean_object* v_es_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_es_1549_ = lean_ctor_get(v_x_1547_, 0);
v___x_1550_ = lean_unsigned_to_nat(0u);
v___x_1551_ = lean_array_get_size(v_es_1549_);
v___x_1552_ = lean_nat_dec_lt(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_dec(v_f_1546_);
return v_x_1548_;
}
else
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_nat_dec_le(v___x_1551_, v___x_1551_);
if (v___x_1553_ == 0)
{
if (v___x_1552_ == 0)
{
lean_dec(v_f_1546_);
return v_x_1548_;
}
else
{
size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = ((size_t)0ULL);
v___x_1555_ = lean_usize_of_nat(v___x_1551_);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1546_, v_es_1549_, v___x_1554_, v___x_1555_, v_x_1548_);
return v___x_1556_;
}
}
else
{
size_t v___x_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = ((size_t)0ULL);
v___x_1558_ = lean_usize_of_nat(v___x_1551_);
v___x_1559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1546_, v_es_1549_, v___x_1557_, v___x_1558_, v_x_1548_);
return v___x_1559_;
}
}
}
else
{
lean_object* v_ks_1560_; lean_object* v_vs_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_ks_1560_ = lean_ctor_get(v_x_1547_, 0);
v_vs_1561_ = lean_ctor_get(v_x_1547_, 1);
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1546_, v_ks_1560_, v_vs_1561_, v___x_1562_, v_x_1548_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1564_, lean_object* v_as_1565_, size_t v_i_1566_, size_t v_stop_1567_, lean_object* v_b_1568_){
_start:
{
lean_object* v___y_1570_; uint8_t v___x_1574_; 
v___x_1574_ = lean_usize_dec_eq(v_i_1566_, v_stop_1567_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_array_uget_borrowed(v_as_1565_, v_i_1566_);
switch(lean_obj_tag(v___x_1575_))
{
case 0:
{
lean_object* v_key_1576_; lean_object* v_val_1577_; lean_object* v___x_1578_; 
v_key_1576_ = lean_ctor_get(v___x_1575_, 0);
v_val_1577_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_f_1564_);
lean_inc(v_val_1577_);
lean_inc(v_key_1576_);
v___x_1578_ = lean_apply_3(v_f_1564_, v_b_1568_, v_key_1576_, v_val_1577_);
v___y_1570_ = v___x_1578_;
goto v___jp_1569_;
}
case 1:
{
lean_object* v_node_1579_; lean_object* v___x_1580_; 
v_node_1579_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_f_1564_);
v___x_1580_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1564_, v_node_1579_, v_b_1568_);
v___y_1570_ = v___x_1580_;
goto v___jp_1569_;
}
default: 
{
v___y_1570_ = v_b_1568_;
goto v___jp_1569_;
}
}
}
else
{
lean_dec(v_f_1564_);
return v_b_1568_;
}
v___jp_1569_:
{
size_t v___x_1571_; size_t v___x_1572_; 
v___x_1571_ = ((size_t)1ULL);
v___x_1572_ = lean_usize_add(v_i_1566_, v___x_1571_);
v_i_1566_ = v___x_1572_;
v_b_1568_ = v___y_1570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1581_, lean_object* v_as_1582_, lean_object* v_i_1583_, lean_object* v_stop_1584_, lean_object* v_b_1585_){
_start:
{
size_t v_i_boxed_1586_; size_t v_stop_boxed_1587_; lean_object* v_res_1588_; 
v_i_boxed_1586_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_stop_boxed_1587_ = lean_unbox_usize(v_stop_1584_);
lean_dec(v_stop_1584_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1581_, v_as_1582_, v_i_boxed_1586_, v_stop_boxed_1587_, v_b_1585_);
lean_dec_ref(v_as_1582_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(lean_object* v_f_1589_, lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1589_, v_x_1590_, v_x_1591_);
lean_dec_ref(v_x_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object* v_d_1593_, lean_object* v_declName_1594_){
_start:
{
lean_object* v_tree_1595_; lean_object* v_erased_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v_tree_1595_ = lean_ctor_get(v_d_1593_, 0);
v_erased_1596_ = lean_ctor_get(v_d_1593_, 1);
lean_inc(v_declName_1594_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1597_, 0, v_declName_1594_);
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1598_, 0, v___f_1597_);
v___x_1599_ = 0;
v___x_1600_ = lean_box(v___x_1599_);
v___x_1601_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v___f_1598_, v_tree_1595_, v___x_1600_);
v___x_1602_ = lean_unbox(v___x_1601_);
if (v___x_1602_ == 0)
{
uint8_t v___x_1603_; 
lean_dec(v_declName_1594_);
v___x_1603_ = lean_unbox(v___x_1601_);
lean_dec(v___x_1601_);
return v___x_1603_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_erased_1596_, v_declName_1594_);
lean_dec(v_declName_1594_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_unbox(v___x_1601_);
lean_dec(v___x_1601_);
return v___x_1605_;
}
else
{
lean_dec(v___x_1601_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object* v_d_1606_, lean_object* v_declName_1607_){
_start:
{
uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_res_1608_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1606_, v_declName_1607_);
lean_dec_ref(v_d_1606_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(lean_object* v_00_u03c3_1610_, lean_object* v_00_u03b1_1611_, lean_object* v_f_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1612_, v_x_1613_, v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(lean_object* v_00_u03c3_1616_, lean_object* v_00_u03b1_1617_, lean_object* v_f_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(v_00_u03c3_1616_, v_00_u03b1_1617_, v_f_1618_, v_x_1619_, v_x_1620_);
lean_dec_ref(v_x_1620_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(lean_object* v_map_1622_, lean_object* v_f_1623_, lean_object* v_init_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1623_, v_map_1622_, v_init_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(lean_object* v_map_1626_, lean_object* v_f_1627_, lean_object* v_init_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(v_map_1626_, v_f_1627_, v_init_1628_);
lean_dec_ref(v_map_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(lean_object* v_00_u03c3_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_map_1632_, lean_object* v_f_1633_, lean_object* v_init_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1633_, v_map_1632_, v_init_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(lean_object* v_00_u03c3_1636_, lean_object* v_00_u03b2_1637_, lean_object* v_map_1638_, lean_object* v_f_1639_, lean_object* v_init_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(v_00_u03c3_1636_, v_00_u03b2_1637_, v_map_1638_, v_f_1639_, v_init_1640_);
lean_dec_ref(v_map_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1643_, v_x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(lean_object* v_00_u03b2_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
uint8_t v_res_1649_; lean_object* v_r_1650_; 
v_res_1649_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(v_00_u03b2_1646_, v_x_1647_, v_x_1648_);
lean_dec(v_x_1648_);
lean_dec_ref(v_x_1647_);
v_r_1650_ = lean_box(v_res_1649_);
return v_r_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(lean_object* v_00_u03b1_1651_, lean_object* v_00_u03c3_1652_, lean_object* v_f_1653_, lean_object* v_as_1654_, size_t v_i_1655_, size_t v_stop_1656_, lean_object* v_b_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1653_, v_as_1654_, v_i_1655_, v_stop_1656_, v_b_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1659_, lean_object* v_00_u03c3_1660_, lean_object* v_f_1661_, lean_object* v_as_1662_, lean_object* v_i_1663_, lean_object* v_stop_1664_, lean_object* v_b_1665_){
_start:
{
size_t v_i_boxed_1666_; size_t v_stop_boxed_1667_; lean_object* v_res_1668_; 
v_i_boxed_1666_ = lean_unbox_usize(v_i_1663_);
lean_dec(v_i_1663_);
v_stop_boxed_1667_ = lean_unbox_usize(v_stop_1664_);
lean_dec(v_stop_1664_);
v_res_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_00_u03b1_1659_, v_00_u03c3_1660_, v_f_1661_, v_as_1662_, v_i_boxed_1666_, v_stop_boxed_1667_, v_b_1665_);
lean_dec_ref(v_as_1662_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03c3_1670_, lean_object* v_f_1671_, lean_object* v_as_1672_, size_t v_i_1673_, size_t v_stop_1674_, lean_object* v_b_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1671_, v_as_1672_, v_i_1673_, v_stop_1674_, v_b_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1677_, lean_object* v_00_u03c3_1678_, lean_object* v_f_1679_, lean_object* v_as_1680_, lean_object* v_i_1681_, lean_object* v_stop_1682_, lean_object* v_b_1683_){
_start:
{
size_t v_i_boxed_1684_; size_t v_stop_boxed_1685_; lean_object* v_res_1686_; 
v_i_boxed_1684_ = lean_unbox_usize(v_i_1681_);
lean_dec(v_i_1681_);
v_stop_boxed_1685_ = lean_unbox_usize(v_stop_1682_);
lean_dec(v_stop_1682_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(v_00_u03b1_1677_, v_00_u03c3_1678_, v_f_1679_, v_as_1680_, v_i_boxed_1684_, v_stop_boxed_1685_, v_b_1683_);
lean_dec_ref(v_as_1680_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(lean_object* v_00_u03c3_1687_, lean_object* v_00_u03b1_1688_, lean_object* v_00_u03b2_1689_, lean_object* v_f_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1690_, v_x_1691_, v_x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1694_, lean_object* v_00_u03b1_1695_, lean_object* v_00_u03b2_1696_, lean_object* v_f_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(v_00_u03c3_1694_, v_00_u03b1_1695_, v_00_u03b2_1696_, v_f_1697_, v_x_1698_, v_x_1699_);
lean_dec_ref(v_x_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(lean_object* v_00_u03b2_1701_, lean_object* v_x_1702_, size_t v_x_1703_, lean_object* v_x_1704_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1702_, v_x_1703_, v_x_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
size_t v_x_1499__boxed_1710_; uint8_t v_res_1711_; lean_object* v_r_1712_; 
v_x_1499__boxed_1710_ = lean_unbox_usize(v_x_1708_);
lean_dec(v_x_1708_);
v_res_1711_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(v_00_u03b2_1706_, v_x_1707_, v_x_1499__boxed_1710_, v_x_1709_);
lean_dec(v_x_1709_);
lean_dec_ref(v_x_1707_);
v_r_1712_ = lean_box(v_res_1711_);
return v_r_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_00_u03c3_1715_, lean_object* v_f_1716_, lean_object* v_as_1717_, size_t v_i_1718_, size_t v_stop_1719_, lean_object* v_b_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1716_, v_as_1717_, v_i_1718_, v_stop_1719_, v_b_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_00_u03b2_1723_, lean_object* v_00_u03c3_1724_, lean_object* v_f_1725_, lean_object* v_as_1726_, lean_object* v_i_1727_, lean_object* v_stop_1728_, lean_object* v_b_1729_){
_start:
{
size_t v_i_boxed_1730_; size_t v_stop_boxed_1731_; lean_object* v_res_1732_; 
v_i_boxed_1730_ = lean_unbox_usize(v_i_1727_);
lean_dec(v_i_1727_);
v_stop_boxed_1731_ = lean_unbox_usize(v_stop_1728_);
lean_dec(v_stop_1728_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(v_00_u03b1_1722_, v_00_u03b2_1723_, v_00_u03c3_1724_, v_f_1725_, v_as_1726_, v_i_boxed_1730_, v_stop_boxed_1731_, v_b_1729_);
lean_dec_ref(v_as_1726_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1733_, lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_f_1736_, lean_object* v_keys_1737_, lean_object* v_vals_1738_, lean_object* v_heq_1739_, lean_object* v_i_1740_, lean_object* v_acc_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1736_, v_keys_1737_, v_vals_1738_, v_i_1740_, v_acc_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1743_, lean_object* v_00_u03b1_1744_, lean_object* v_00_u03b2_1745_, lean_object* v_f_1746_, lean_object* v_keys_1747_, lean_object* v_vals_1748_, lean_object* v_heq_1749_, lean_object* v_i_1750_, lean_object* v_acc_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(v_00_u03c3_1743_, v_00_u03b1_1744_, v_00_u03b2_1745_, v_f_1746_, v_keys_1747_, v_vals_1748_, v_heq_1749_, v_i_1750_, v_acc_1751_);
lean_dec_ref(v_vals_1748_);
lean_dec_ref(v_keys_1747_);
return v_res_1752_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1753_, lean_object* v_keys_1754_, lean_object* v_vals_1755_, lean_object* v_heq_1756_, lean_object* v_i_1757_, lean_object* v_k_1758_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1754_, v_i_1757_, v_k_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1760_, lean_object* v_keys_1761_, lean_object* v_vals_1762_, lean_object* v_heq_1763_, lean_object* v_i_1764_, lean_object* v_k_1765_){
_start:
{
uint8_t v_res_1766_; lean_object* v_r_1767_; 
v_res_1766_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(v_00_u03b2_1760_, v_keys_1761_, v_vals_1762_, v_heq_1763_, v_i_1764_, v_k_1765_);
lean_dec(v_k_1765_);
lean_dec_ref(v_vals_1762_);
lean_dec_ref(v_keys_1761_);
v_r_1767_ = lean_box(v_res_1766_);
return v_r_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg(lean_object* v_declName_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v_env_1772_; lean_object* v___x_1773_; lean_object* v_ext_1774_; lean_object* v_toEnvExtension_1775_; lean_object* v_asyncMode_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1771_ = lean_st_ref_get(v_a_1769_);
v_env_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_ref(v_env_1772_);
lean_dec(v___x_1771_);
v___x_1773_ = l_Lean_Meta_Ext_extExtension;
v_ext_1774_ = lean_ctor_get(v___x_1773_, 1);
v_toEnvExtension_1775_ = lean_ctor_get(v_ext_1774_, 0);
v_asyncMode_1776_ = lean_ctor_get(v_toEnvExtension_1775_, 2);
v___x_1777_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1778_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1777_, v___x_1773_, v_env_1772_, v_asyncMode_1776_);
v___x_1779_ = l_Lean_Meta_Ext_ExtTheorems_contains(v___x_1778_, v_declName_1768_);
lean_dec(v___x_1778_);
v___x_1780_ = lean_box(v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg___boxed(lean_object* v_declName_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1782_, v_a_1783_);
lean_dec(v_a_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object* v_declName_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1786_, v_a_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object* v_declName_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Meta_Ext_isExtTheorem(v_declName_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(lean_object* v_d_1796_, lean_object* v_declName_1797_, lean_object* v_toPure_1798_, lean_object* v_____r_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = l_Lean_Meta_Ext_ExtTheorems_eraseCore(v_d_1796_, v_declName_1797_);
v___x_1801_ = lean_apply_2(v_toPure_1798_, lean_box(0), v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1(lean_object* v___f_1802_, lean_object* v_____r_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_apply_1(v___f_1802_, v_____r_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg(lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_d_1813_, lean_object* v_declName_1814_){
_start:
{
lean_object* v_toApplicative_1815_; lean_object* v_toBind_1816_; lean_object* v_toPure_1817_; lean_object* v___f_1818_; uint8_t v___x_1819_; 
v_toApplicative_1815_ = lean_ctor_get(v_inst_1811_, 0);
v_toBind_1816_ = lean_ctor_get(v_inst_1811_, 1);
lean_inc(v_toBind_1816_);
v_toPure_1817_ = lean_ctor_get(v_toApplicative_1815_, 1);
lean_inc(v_toPure_1817_);
lean_inc_n(v_declName_1814_, 2);
lean_inc_ref(v_d_1813_);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1818_, 0, v_d_1813_);
lean_closure_set(v___f_1818_, 1, v_declName_1814_);
lean_closure_set(v___f_1818_, 2, v_toPure_1817_);
v___x_1819_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1813_, v_declName_1814_);
if (v___x_1819_ == 0)
{
lean_object* v___f_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v_d_1813_);
v___f_1820_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1820_, 0, v___f_1818_);
v___x_1821_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1);
v___x_1822_ = l_Lean_MessageData_ofConstName(v_declName_1814_, v___x_1819_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_throwError___redArg(v_inst_1811_, v_inst_1812_, v___x_1825_);
v___x_1827_ = lean_apply_4(v_toBind_1816_, lean_box(0), lean_box(0), v___x_1826_, v___f_1820_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_inc(v_toPure_1817_);
lean_dec_ref(v___f_1818_);
lean_dec(v_toBind_1816_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_inst_1811_);
v___x_1828_ = lean_box(0);
v___x_1829_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(v_d_1813_, v_declName_1814_, v_toPure_1817_, v___x_1828_);
return v___x_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object* v_m_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_d_1833_, lean_object* v_declName_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg(v_inst_1831_, v_inst_1832_, v_d_1833_, v_declName_1834_);
return v___x_1835_;
}
}
lean_object* runtime_initialize_Init_Data_Array_InsertionSort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Ext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
