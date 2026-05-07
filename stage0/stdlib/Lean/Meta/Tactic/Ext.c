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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_46_);
v___x_51_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Ext_instReprExtTheorem_repr_spec__0_spec__0___lam__0(v_head_50_);
return v___x_51_;
}
else
{
lean_object* v_head_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc(v_tail_49_);
v_head_52_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_52_);
lean_dec_ref(v_x_46_);
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16(lean_object* v_xs_295_, lean_object* v_v_296_, lean_object* v_i_297_){
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
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16___boxed(lean_object* v_xs_307_, lean_object* v_v_308_, lean_object* v_i_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16(v_xs_307_, v_v_308_, v_i_309_);
lean_dec(v_v_308_);
lean_dec_ref(v_xs_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10(lean_object* v_xs_311_, lean_object* v_v_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10_spec__16(v_xs_311_, v_v_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10___boxed(lean_object* v_xs_315_, lean_object* v_v_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10(v_xs_315_, v_v_316_);
lean_dec(v_v_316_);
lean_dec_ref(v_xs_315_);
return v_res_317_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; 
v___x_318_ = ((size_t)5ULL);
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_shift_left(v___x_319_, v___x_318_);
return v___x_320_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; 
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__0);
v___x_323_ = lean_usize_sub(v___x_322_, v___x_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(lean_object* v_x_324_, size_t v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v_es_327_; lean_object* v___x_328_; size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v_j_332_; lean_object* v_entry_333_; 
v_es_327_ = lean_ctor_get(v_x_324_, 0);
v___x_328_ = lean_box(2);
v___x_329_ = ((size_t)5ULL);
v___x_330_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
v___x_331_ = lean_usize_land(v_x_325_, v___x_330_);
v_j_332_ = lean_usize_to_nat(v___x_331_);
v_entry_333_ = lean_array_get(v___x_328_, v_es_327_, v_j_332_);
switch(lean_obj_tag(v_entry_333_))
{
case 0:
{
lean_object* v_key_334_; uint8_t v___x_335_; 
v_key_334_ = lean_ctor_get(v_entry_333_, 0);
lean_inc(v_key_334_);
lean_dec_ref(v_entry_333_);
v___x_335_ = lean_name_eq(v_x_326_, v_key_334_);
lean_dec(v_key_334_);
if (v___x_335_ == 0)
{
lean_dec(v_j_332_);
return v_x_324_;
}
else
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
lean_inc_ref(v_es_327_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_x_324_, 0);
lean_dec(v_unused_344_);
v___x_337_ = v_x_324_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_dec(v_x_324_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_array_set(v_es_327_, v_j_332_, v___x_328_);
lean_dec(v_j_332_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
case 1:
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_378_; 
lean_inc_ref(v_es_327_);
v_isSharedCheck_378_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_x_324_, 0);
lean_dec(v_unused_379_);
v___x_346_ = v_x_324_;
v_isShared_347_ = v_isSharedCheck_378_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_x_324_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_378_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_node_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_377_; 
v_node_348_ = lean_ctor_get(v_entry_333_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_entry_333_);
if (v_isSharedCheck_377_ == 0)
{
v___x_350_ = v_entry_333_;
v_isShared_351_ = v_isSharedCheck_377_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_node_348_);
lean_dec(v_entry_333_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_377_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_entries_352_; size_t v___x_353_; lean_object* v_newNode_354_; lean_object* v___x_355_; 
v_entries_352_ = lean_array_set(v_es_327_, v_j_332_, v___x_328_);
v___x_353_ = lean_usize_shift_right(v_x_325_, v___x_329_);
v_newNode_354_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_node_348_, v___x_353_, v_x_326_);
lean_inc_ref(v_newNode_354_);
v___x_355_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v___x_357_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v_newNode_354_);
v___x_357_ = v___x_350_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_newNode_354_);
v___x_357_ = v_reuseFailAlloc_362_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_358_ = lean_array_set(v_entries_352_, v_j_332_, v___x_357_);
lean_dec(v_j_332_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_358_);
v___x_360_ = v___x_346_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v_val_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v_newNode_354_);
lean_del_object(v___x_350_);
v_val_363_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_363_);
lean_dec_ref(v___x_355_);
v_fst_364_ = lean_ctor_get(v_val_363_, 0);
v_snd_365_ = lean_ctor_get(v_val_363_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_val_363_);
if (v_isSharedCheck_376_ == 0)
{
v___x_367_ = v_val_363_;
v_isShared_368_ = v_isSharedCheck_376_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_snd_365_);
lean_inc(v_fst_364_);
lean_dec(v_val_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_376_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_fst_364_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_snd_365_);
v___x_370_ = v_reuseFailAlloc_375_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_array_set(v_entries_352_, v_j_332_, v___x_370_);
lean_dec(v_j_332_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_371_);
v___x_373_ = v___x_346_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_332_);
return v_x_324_;
}
}
}
else
{
lean_object* v_ks_380_; lean_object* v_vs_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_395_; 
v_ks_380_ = lean_ctor_get(v_x_324_, 0);
v_vs_381_ = lean_ctor_get(v_x_324_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_395_ == 0)
{
v___x_383_ = v_x_324_;
v_isShared_384_ = v_isSharedCheck_395_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_vs_381_);
lean_inc(v_ks_380_);
lean_dec(v_x_324_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_395_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; 
v___x_385_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5_spec__10(v_ks_380_, v_x_326_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_387_; 
if (v_isShared_384_ == 0)
{
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_ks_380_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_vs_381_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
else
{
lean_object* v_val_389_; lean_object* v_keys_x27_390_; lean_object* v_vals_x27_391_; lean_object* v___x_393_; 
v_val_389_ = lean_ctor_get(v___x_385_, 0);
lean_inc_n(v_val_389_, 2);
lean_dec_ref(v___x_385_);
v_keys_x27_390_ = l_Array_eraseIdx___redArg(v_ks_380_, v_val_389_);
v_vals_x27_391_ = l_Array_eraseIdx___redArg(v_vs_381_, v_val_389_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_vals_x27_391_);
lean_ctor_set(v___x_383_, 0, v_keys_x27_390_);
v___x_393_ = v___x_383_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_keys_x27_390_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_vals_x27_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___boxed(lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
size_t v_x_1770__boxed_399_; lean_object* v_res_400_; 
v_x_1770__boxed_399_ = lean_unbox_usize(v_x_397_);
lean_dec(v_x_397_);
v_res_400_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_x_396_, v_x_1770__boxed_399_, v_x_398_);
lean_dec(v_x_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
uint64_t v___y_404_; 
if (lean_obj_tag(v_x_402_) == 0)
{
uint64_t v___x_407_; 
v___x_407_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_404_ = v___x_407_;
goto v___jp_403_;
}
else
{
uint64_t v_hash_408_; 
v_hash_408_ = lean_ctor_get_uint64(v_x_402_, sizeof(void*)*2);
v___y_404_ = v_hash_408_;
goto v___jp_403_;
}
v___jp_403_:
{
size_t v_h_405_; lean_object* v___x_406_; 
v_h_405_ = lean_uint64_to_usize(v___y_404_);
v___x_406_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_x_401_, v_h_405_, v_x_402_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_409_, v_x_410_);
lean_dec(v_x_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_412_, lean_object* v_vals_413_, lean_object* v_i_414_, lean_object* v_k_415_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_array_get_size(v_keys_412_);
v___x_417_ = lean_nat_dec_lt(v_i_414_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec(v_i_414_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
else
{
lean_object* v_k_x27_419_; uint8_t v___x_420_; 
v_k_x27_419_ = lean_array_fget_borrowed(v_keys_412_, v_i_414_);
v___x_420_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_415_, v_k_x27_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_i_414_, v___x_421_);
lean_dec(v_i_414_);
v_i_414_ = v___x_422_;
goto _start;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_array_fget_borrowed(v_vals_413_, v_i_414_);
lean_dec(v_i_414_);
lean_inc(v___x_424_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_426_, lean_object* v_vals_427_, lean_object* v_i_428_, lean_object* v_k_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_keys_426_, v_vals_427_, v_i_428_, v_k_429_);
lean_dec(v_k_429_);
lean_dec_ref(v_vals_427_);
lean_dec_ref(v_keys_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_431_, size_t v_x_432_, lean_object* v_x_433_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v_es_434_; lean_object* v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; lean_object* v_j_439_; lean_object* v___x_440_; 
v_es_434_ = lean_ctor_get(v_x_431_, 0);
v___x_435_ = lean_box(2);
v___x_436_ = ((size_t)5ULL);
v___x_437_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
v___x_438_ = lean_usize_land(v_x_432_, v___x_437_);
v_j_439_ = lean_usize_to_nat(v___x_438_);
v___x_440_ = lean_array_get_borrowed(v___x_435_, v_es_434_, v_j_439_);
lean_dec(v_j_439_);
switch(lean_obj_tag(v___x_440_))
{
case 0:
{
lean_object* v_key_441_; lean_object* v_val_442_; uint8_t v___x_443_; 
v_key_441_ = lean_ctor_get(v___x_440_, 0);
v_val_442_ = lean_ctor_get(v___x_440_, 1);
v___x_443_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_433_, v_key_441_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = lean_box(0);
return v___x_444_;
}
else
{
lean_object* v___x_445_; 
lean_inc(v_val_442_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v_val_442_);
return v___x_445_;
}
}
case 1:
{
lean_object* v_node_446_; size_t v___x_447_; 
v_node_446_ = lean_ctor_get(v___x_440_, 0);
v___x_447_ = lean_usize_shift_right(v_x_432_, v___x_436_);
v_x_431_ = v_node_446_;
v_x_432_ = v___x_447_;
goto _start;
}
default: 
{
lean_object* v___x_449_; 
v___x_449_ = lean_box(0);
return v___x_449_;
}
}
}
else
{
lean_object* v_ks_450_; lean_object* v_vs_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_ks_450_ = lean_ctor_get(v_x_431_, 0);
v_vs_451_ = lean_ctor_get(v_x_431_, 1);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ks_450_, v_vs_451_, v___x_452_, v_x_433_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
size_t v_x_1953__boxed_457_; lean_object* v_res_458_; 
v_x_1953__boxed_457_ = lean_unbox_usize(v_x_455_);
lean_dec(v_x_455_);
v_res_458_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_454_, v_x_1953__boxed_457_, v_x_456_);
lean_dec(v_x_456_);
lean_dec_ref(v_x_454_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
uint64_t v___x_461_; size_t v___x_462_; lean_object* v___x_463_; 
v___x_461_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_460_);
v___x_462_ = lean_uint64_to_usize(v___x_461_);
v___x_463_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_459_, v___x_462_, v_x_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec_ref(v_x_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__11(lean_object* v_vs_467_, lean_object* v_v_468_, lean_object* v_i_469_){
_start:
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_array_get_size(v_vs_467_);
v___x_471_ = lean_nat_dec_lt(v_i_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v_i_469_);
v___x_472_ = lean_array_push(v_vs_467_, v_v_468_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_array_fget_borrowed(v_vs_467_, v_i_469_);
v___x_474_ = l_Lean_Meta_Ext_instBEqExtTheorem_beq(v_v_468_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_add(v_i_469_, v___x_475_);
lean_dec(v_i_469_);
v_i_469_ = v___x_476_;
goto _start;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = lean_array_fset(v_vs_467_, v_i_469_, v_v_468_);
lean_dec(v_i_469_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5(lean_object* v_vs_479_, lean_object* v_v_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5_spec__11(v_vs_479_, v_v_480_, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(lean_object* v_x_483_, lean_object* v_keys_484_, lean_object* v_v_485_, lean_object* v_k_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v_c_490_; lean_object* v___x_491_; 
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_x_483_, v___x_488_);
v_c_490_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_484_, v_v_485_, v___x_489_);
lean_dec(v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_491_, 0, v_k_486_);
lean_ctor_set(v___x_491_, 1, v_c_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_492_, lean_object* v_keys_493_, lean_object* v_v_494_, lean_object* v_k_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_492_, v_keys_493_, v_v_494_, v_k_495_, v_x_496_);
lean_dec_ref(v_keys_493_);
lean_dec(v_x_492_);
return v_res_497_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(lean_object* v_a_498_, lean_object* v_b_499_){
_start:
{
lean_object* v_fst_500_; lean_object* v_fst_501_; uint8_t v___x_502_; 
v_fst_500_ = lean_ctor_get(v_a_498_, 0);
v_fst_501_ = lean_ctor_get(v_b_499_, 0);
v___x_502_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_500_, v_fst_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_a_503_, v_b_504_);
lean_dec_ref(v_b_504_);
lean_dec_ref(v_a_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(lean_object* v_x_511_, lean_object* v_keys_512_, lean_object* v_v_513_, lean_object* v_k_514_, lean_object* v_as_515_, lean_object* v_k_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_mid_521_; lean_object* v_midVal_522_; uint8_t v___x_523_; 
v___x_519_ = lean_nat_add(v_x_517_, v_x_518_);
v___x_520_ = lean_unsigned_to_nat(1u);
v_mid_521_ = lean_nat_shiftr(v___x_519_, v___x_520_);
lean_dec(v___x_519_);
v_midVal_522_ = lean_array_fget(v_as_515_, v_mid_521_);
v___x_523_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_midVal_522_, v_k_516_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
lean_dec(v_x_518_);
v___x_524_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_516_, v_midVal_522_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
lean_dec(v_x_517_);
v___x_525_ = lean_array_get_size(v_as_515_);
v___x_526_ = lean_nat_dec_lt(v_mid_521_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec(v_midVal_522_);
lean_dec(v_mid_521_);
lean_dec(v_k_514_);
lean_dec_ref(v_v_513_);
return v_as_515_;
}
else
{
lean_object* v_snd_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_539_; 
v_snd_527_ = lean_ctor_get(v_midVal_522_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_midVal_522_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v_midVal_522_, 0);
lean_dec(v_unused_540_);
v___x_529_ = v_midVal_522_;
v_isShared_530_ = v_isSharedCheck_539_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snd_527_);
lean_dec(v_midVal_522_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_539_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v_xs_x27_532_; lean_object* v___x_533_; lean_object* v_c_534_; lean_object* v___x_536_; 
v___x_531_ = lean_box(0);
v_xs_x27_532_ = lean_array_fset(v_as_515_, v_mid_521_, v___x_531_);
v___x_533_ = lean_nat_add(v_x_511_, v___x_520_);
v_c_534_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_512_, v_v_513_, v___x_533_, v_snd_527_);
lean_dec(v___x_533_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_c_534_);
lean_ctor_set(v___x_529_, 0, v_k_514_);
v___x_536_ = v___x_529_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_k_514_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_c_534_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = lean_array_fset(v_xs_x27_532_, v_mid_521_, v___x_536_);
lean_dec(v_mid_521_);
return v___x_537_;
}
}
}
}
else
{
lean_dec(v_midVal_522_);
v_x_518_ = v_mid_521_;
goto _start;
}
}
else
{
uint8_t v___x_542_; 
lean_dec(v_midVal_522_);
v___x_542_ = lean_nat_dec_eq(v_mid_521_, v_x_517_);
if (v___x_542_ == 0)
{
lean_dec(v_x_517_);
v_x_517_ = v_mid_521_;
goto _start;
}
else
{
lean_object* v___x_544_; lean_object* v_c_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_j_548_; lean_object* v_as_549_; lean_object* v___x_550_; 
lean_dec(v_mid_521_);
lean_dec(v_x_518_);
v___x_544_ = lean_nat_add(v_x_511_, v___x_520_);
v_c_545_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_512_, v_v_513_, v___x_544_);
lean_dec(v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v_k_514_);
lean_ctor_set(v___x_546_, 1, v_c_545_);
v___x_547_ = lean_nat_add(v_x_517_, v___x_520_);
lean_dec(v_x_517_);
v_j_548_ = lean_array_get_size(v_as_515_);
v_as_549_ = lean_array_push(v_as_515_, v___x_546_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_547_, v_as_549_, v_j_548_);
lean_dec(v___x_547_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6(lean_object* v_x_551_, lean_object* v_keys_552_, lean_object* v_v_553_, lean_object* v_k_554_, lean_object* v_as_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_array_get_size(v_as_555_);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_nat_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_array_fget_borrowed(v_as_555_, v___x_558_);
v___x_561_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_556_, v___x_560_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; 
v___x_562_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_560_, v_k_556_);
if (v___x_562_ == 0)
{
uint8_t v___x_563_; 
v___x_563_ = lean_nat_dec_lt(v___x_558_, v___x_557_);
if (v___x_563_ == 0)
{
lean_dec(v_k_554_);
lean_dec_ref(v_v_553_);
return v_as_555_;
}
else
{
lean_object* v___x_564_; lean_object* v_xs_x27_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_inc(v___x_560_);
v___x_564_ = lean_box(0);
v_xs_x27_565_ = lean_array_fset(v_as_555_, v___x_558_, v___x_564_);
v___x_566_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_551_, v_keys_552_, v_v_553_, v_k_554_, v___x_560_);
v___x_567_ = lean_array_fset(v_xs_x27_565_, v___x_558_, v___x_566_);
return v___x_567_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_sub(v___x_557_, v___x_568_);
v___x_570_ = lean_array_fget_borrowed(v_as_555_, v___x_569_);
v___x_571_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v___x_570_, v_k_556_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
v___x_572_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__1(v_k_556_, v___x_570_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
v___x_573_ = lean_nat_dec_lt(v___x_569_, v___x_557_);
if (v___x_573_ == 0)
{
lean_dec(v___x_569_);
lean_dec(v_k_554_);
lean_dec_ref(v_v_553_);
return v_as_555_;
}
else
{
lean_object* v___x_574_; lean_object* v_xs_x27_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_inc(v___x_570_);
v___x_574_ = lean_box(0);
v_xs_x27_575_ = lean_array_fset(v_as_555_, v___x_569_, v___x_574_);
v___x_576_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_551_, v_keys_552_, v_v_553_, v_k_554_, v___x_570_);
v___x_577_ = lean_array_fset(v_xs_x27_575_, v___x_569_, v___x_576_);
lean_dec(v___x_569_);
return v___x_577_;
}
}
else
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(v_x_551_, v_keys_552_, v_v_553_, v_k_554_, v_as_555_, v_k_556_, v___x_558_, v___x_569_);
return v___x_578_;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___x_569_);
v___x_579_ = lean_box(0);
v___x_580_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_551_, v_keys_552_, v_v_553_, v_k_554_, v___x_579_);
v___x_581_ = lean_array_push(v_as_555_, v___x_580_);
return v___x_581_;
}
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_as_584_; lean_object* v___x_585_; 
v___x_582_ = lean_box(0);
v___x_583_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_551_, v_keys_552_, v_v_553_, v_k_554_, v___x_582_);
v_as_584_ = lean_array_push(v_as_555_, v___x_583_);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_558_, v_as_584_, v___x_557_);
return v___x_585_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
v___x_587_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__0(v_x_551_, v_keys_552_, v_v_553_, v_k_554_, v___x_586_);
v___x_588_ = lean_array_push(v_as_555_, v___x_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_keys_589_, lean_object* v_v_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_vs_593_; lean_object* v_children_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_611_; 
v_vs_593_ = lean_ctor_get(v_x_592_, 0);
v_children_594_ = lean_ctor_get(v_x_592_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_592_);
if (v_isSharedCheck_611_ == 0)
{
v___x_596_ = v_x_592_;
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_children_594_);
lean_inc(v_vs_593_);
lean_dec(v_x_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_get_size(v_keys_589_);
v___x_599_ = lean_nat_dec_lt(v_x_591_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__5(v_vs_593_, v_v_590_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_600_);
v___x_602_ = v___x_596_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_children_594_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
else
{
lean_object* v_k_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v_c_607_; lean_object* v___x_609_; 
v_k_604_ = lean_array_fget_borrowed(v_keys_589_, v_x_591_);
v___x_605_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__1));
lean_inc_n(v_k_604_, 2);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_k_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v_c_607_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_591_, v_keys_589_, v_v_590_, v_k_604_, v_children_594_, v___x_606_);
lean_dec_ref(v___x_606_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_c_607_);
v___x_609_ = v___x_596_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_vs_593_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_c_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(lean_object* v_x_612_, lean_object* v_keys_613_, lean_object* v_v_614_, lean_object* v_k_615_, lean_object* v_x_616_){
_start:
{
lean_object* v_snd_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_627_; 
v_snd_617_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_x_616_, 0);
lean_dec(v_unused_628_);
v___x_619_ = v_x_616_;
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snd_617_);
lean_dec(v_x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_c_623_; lean_object* v___x_625_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_x_612_, v___x_621_);
v_c_623_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_613_, v_v_614_, v___x_622_, v_snd_617_);
lean_dec(v___x_622_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v_c_623_);
lean_ctor_set(v___x_619_, 0, v_k_615_);
v___x_625_ = v___x_619_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_k_615_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_c_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_629_, lean_object* v_keys_630_, lean_object* v_v_631_, lean_object* v_k_632_, lean_object* v_x_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___lam__2(v_x_629_, v_keys_630_, v_v_631_, v_k_632_, v_x_633_);
lean_dec_ref(v_keys_630_);
lean_dec(v_x_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___boxed(lean_object* v_keys_635_, lean_object* v_v_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_635_, v_v_636_, v_x_637_, v_x_638_);
lean_dec(v_x_637_);
lean_dec_ref(v_keys_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_x_640_, lean_object* v_keys_641_, lean_object* v_v_642_, lean_object* v_k_643_, lean_object* v_as_644_, lean_object* v_k_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(v_x_640_, v_keys_641_, v_v_642_, v_k_643_, v_as_644_, v_k_645_, v_x_646_, v_x_647_);
lean_dec_ref(v_k_645_);
lean_dec_ref(v_keys_641_);
lean_dec(v_x_640_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6___boxed(lean_object* v_x_649_, lean_object* v_keys_650_, lean_object* v_v_651_, lean_object* v_k_652_, lean_object* v_as_653_, lean_object* v_k_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6(v_x_649_, v_keys_650_, v_v_651_, v_k_652_, v_as_653_, v_k_654_);
lean_dec_ref(v_k_654_);
lean_dec_ref(v_keys_650_);
lean_dec(v_x_649_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10___redArg(lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_ks_660_; lean_object* v_vs_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_685_; 
v_ks_660_ = lean_ctor_get(v_x_656_, 0);
v_vs_661_ = lean_ctor_get(v_x_656_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_685_ == 0)
{
v___x_663_ = v_x_656_;
v_isShared_664_ = v_isSharedCheck_685_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_vs_661_);
lean_inc(v_ks_660_);
lean_dec(v_x_656_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_685_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_array_get_size(v_ks_660_);
v___x_666_ = lean_nat_dec_lt(v_x_657_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec(v_x_657_);
v___x_667_ = lean_array_push(v_ks_660_, v_x_658_);
v___x_668_ = lean_array_push(v_vs_661_, v_x_659_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_668_);
lean_ctor_set(v___x_663_, 0, v___x_667_);
v___x_670_ = v___x_663_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
lean_object* v_k_x27_672_; uint8_t v___x_673_; 
v_k_x27_672_ = lean_array_fget_borrowed(v_ks_660_, v_x_657_);
v___x_673_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_658_, v_k_x27_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_675_; 
if (v_isShared_664_ == 0)
{
v___x_675_ = v___x_663_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_ks_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_vs_661_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_x_657_, v___x_676_);
lean_dec(v_x_657_);
v_x_656_ = v___x_675_;
v_x_657_ = v___x_677_;
goto _start;
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_680_ = lean_array_fset(v_ks_660_, v_x_657_, v_x_658_);
v___x_681_ = lean_array_fset(v_vs_661_, v_x_657_, v_x_659_);
lean_dec(v_x_657_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_681_);
lean_ctor_set(v___x_663_, 0, v___x_680_);
v___x_683_ = v___x_663_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_n_686_, lean_object* v_k_687_, lean_object* v_v_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_n_686_, v___x_689_, v_k_687_, v_v_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object* v_x_692_, size_t v_x_693_, size_t v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_692_) == 0)
{
lean_object* v_es_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; lean_object* v_j_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_es_697_ = lean_ctor_get(v_x_692_, 0);
v___x_698_ = ((size_t)5ULL);
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
v___x_701_ = lean_usize_land(v_x_693_, v___x_700_);
v_j_702_ = lean_usize_to_nat(v___x_701_);
v___x_703_ = lean_array_get_size(v_es_697_);
v___x_704_ = lean_nat_dec_lt(v_j_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_dec(v_j_702_);
lean_dec(v_x_696_);
lean_dec(v_x_695_);
return v_x_692_;
}
else
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_741_; 
lean_inc_ref(v_es_697_);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_692_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_x_692_, 0);
lean_dec(v_unused_742_);
v___x_706_ = v_x_692_;
v_isShared_707_ = v_isSharedCheck_741_;
goto v_resetjp_705_;
}
else
{
lean_dec(v_x_692_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_741_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_v_708_; lean_object* v___x_709_; lean_object* v_xs_x27_710_; lean_object* v___y_712_; 
v_v_708_ = lean_array_fget(v_es_697_, v_j_702_);
v___x_709_ = lean_box(0);
v_xs_x27_710_ = lean_array_fset(v_es_697_, v_j_702_, v___x_709_);
switch(lean_obj_tag(v_v_708_))
{
case 0:
{
lean_object* v_key_717_; lean_object* v_val_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_728_; 
v_key_717_ = lean_ctor_get(v_v_708_, 0);
v_val_718_ = lean_ctor_get(v_v_708_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_v_708_);
if (v_isSharedCheck_728_ == 0)
{
v___x_720_ = v_v_708_;
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_val_718_);
lean_inc(v_key_717_);
lean_dec(v_v_708_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_695_, v_key_717_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_del_object(v___x_720_);
v___x_723_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_717_, v_val_718_, v_x_695_, v_x_696_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___y_712_ = v___x_724_;
goto v___jp_711_;
}
else
{
lean_object* v___x_726_; 
lean_dec(v_val_718_);
lean_dec(v_key_717_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_x_696_);
lean_ctor_set(v___x_720_, 0, v_x_695_);
v___x_726_ = v___x_720_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_x_695_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_x_696_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
v___y_712_ = v___x_726_;
goto v___jp_711_;
}
}
}
}
case 1:
{
lean_object* v_node_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_739_; 
v_node_729_ = lean_ctor_get(v_v_708_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_v_708_);
if (v_isSharedCheck_739_ == 0)
{
v___x_731_ = v_v_708_;
v_isShared_732_ = v_isSharedCheck_739_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_node_729_);
lean_dec(v_v_708_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_739_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_733_ = lean_usize_shift_right(v_x_693_, v___x_698_);
v___x_734_ = lean_usize_add(v_x_694_, v___x_699_);
v___x_735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_node_729_, v___x_733_, v___x_734_, v_x_695_, v_x_696_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_735_);
v___x_737_ = v___x_731_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
v___y_712_ = v___x_737_;
goto v___jp_711_;
}
}
}
default: 
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_x_695_);
lean_ctor_set(v___x_740_, 1, v_x_696_);
v___y_712_ = v___x_740_;
goto v___jp_711_;
}
}
v___jp_711_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_array_fset(v_xs_x27_710_, v_j_702_, v___y_712_);
lean_dec(v_j_702_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_713_);
v___x_715_ = v___x_706_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
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
else
{
lean_object* v_ks_743_; lean_object* v_vs_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_764_; 
v_ks_743_ = lean_ctor_get(v_x_692_, 0);
v_vs_744_ = lean_ctor_get(v_x_692_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_692_);
if (v_isSharedCheck_764_ == 0)
{
v___x_746_ = v_x_692_;
v_isShared_747_ = v_isSharedCheck_764_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_vs_744_);
lean_inc(v_ks_743_);
lean_dec(v_x_692_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_764_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_ks_743_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_vs_744_);
v___x_749_ = v_reuseFailAlloc_763_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v_newNode_750_; uint8_t v___y_752_; size_t v___x_758_; uint8_t v___x_759_; 
v_newNode_750_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v___x_749_, v_x_695_, v_x_696_);
v___x_758_ = ((size_t)7ULL);
v___x_759_ = lean_usize_dec_le(v___x_758_, v_x_694_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_750_);
v___x_761_ = lean_unsigned_to_nat(4u);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
lean_dec(v___x_760_);
v___y_752_ = v___x_762_;
goto v___jp_751_;
}
else
{
v___y_752_ = v___x_759_;
goto v___jp_751_;
}
v___jp_751_:
{
if (v___y_752_ == 0)
{
lean_object* v_ks_753_; lean_object* v_vs_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_ks_753_ = lean_ctor_get(v_newNode_750_, 0);
lean_inc_ref(v_ks_753_);
v_vs_754_ = lean_ctor_get(v_newNode_750_, 1);
lean_inc_ref(v_vs_754_);
lean_dec_ref(v_newNode_750_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___closed__0);
v___x_757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(v_x_694_, v_ks_753_, v_vs_754_, v___x_755_, v___x_756_);
lean_dec_ref(v_vs_754_);
lean_dec_ref(v_ks_753_);
return v___x_757_;
}
else
{
return v_newNode_750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(size_t v_depth_765_, lean_object* v_keys_766_, lean_object* v_vals_767_, lean_object* v_i_768_, lean_object* v_entries_769_){
_start:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v_keys_766_);
v___x_771_ = lean_nat_dec_lt(v_i_768_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v_i_768_);
return v_entries_769_;
}
else
{
lean_object* v_k_772_; lean_object* v_v_773_; uint64_t v___x_774_; size_t v_h_775_; size_t v___x_776_; lean_object* v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v_h_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_k_772_ = lean_array_fget_borrowed(v_keys_766_, v_i_768_);
v_v_773_ = lean_array_fget_borrowed(v_vals_767_, v_i_768_);
v___x_774_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_772_);
v_h_775_ = lean_uint64_to_usize(v___x_774_);
v___x_776_ = ((size_t)5ULL);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_sub(v_depth_765_, v___x_778_);
v___x_780_ = lean_usize_mul(v___x_776_, v___x_779_);
v_h_781_ = lean_usize_shift_right(v_h_775_, v___x_780_);
v___x_782_ = lean_nat_add(v_i_768_, v___x_777_);
lean_dec(v_i_768_);
lean_inc(v_v_773_);
lean_inc(v_k_772_);
v___x_783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_entries_769_, v_h_781_, v_depth_765_, v_k_772_, v_v_773_);
v_i_768_ = v___x_782_;
v_entries_769_ = v___x_783_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_depth_785_, lean_object* v_keys_786_, lean_object* v_vals_787_, lean_object* v_i_788_, lean_object* v_entries_789_){
_start:
{
size_t v_depth_boxed_790_; lean_object* v_res_791_; 
v_depth_boxed_790_ = lean_unbox_usize(v_depth_785_);
lean_dec(v_depth_785_);
v_res_791_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(v_depth_boxed_790_, v_keys_786_, v_vals_787_, v_i_788_, v_entries_789_);
lean_dec_ref(v_vals_787_);
lean_dec_ref(v_keys_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
size_t v_x_2336__boxed_797_; size_t v_x_2337__boxed_798_; lean_object* v_res_799_; 
v_x_2336__boxed_797_ = lean_unbox_usize(v_x_793_);
lean_dec(v_x_793_);
v_x_2337__boxed_798_ = lean_unbox_usize(v_x_794_);
lean_dec(v_x_794_);
v_res_799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_792_, v_x_2336__boxed_797_, v_x_2337__boxed_798_, v_x_795_, v_x_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
uint64_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_803_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_801_);
v___x_804_ = lean_uint64_to_usize(v___x_803_);
v___x_805_ = ((size_t)1ULL);
v___x_806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_800_, v___x_804_, v___x_805_, v_x_801_, v_x_802_);
return v___x_806_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3(lean_object* v_msg_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3___closed__0);
v___x_810_ = lean_panic_fn_borrowed(v___x_809_, v_msg_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_814_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2));
v___x_815_ = lean_unsigned_to_nat(23u);
v___x_816_ = lean_unsigned_to_nat(166u);
v___x_817_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1));
v___x_818_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0));
v___x_819_ = l_mkPanicMessageWithDecl(v___x_818_, v___x_817_, v___x_816_, v___x_815_, v___x_814_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(lean_object* v_d_820_, lean_object* v_keys_821_, lean_object* v_v_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_array_get_size(v_keys_821_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_nat_dec_eq(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v_k_827_; lean_object* v___x_828_; 
v___x_826_ = lean_box(0);
v_k_827_ = lean_array_get_borrowed(v___x_826_, v_keys_821_, v___x_824_);
v___x_828_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(v_d_820_, v_k_827_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; lean_object* v_c_830_; lean_object* v___x_831_; 
v___x_829_ = lean_unsigned_to_nat(1u);
v_c_830_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_821_, v_v_822_, v___x_829_);
lean_inc(v_k_827_);
v___x_831_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_820_, v_k_827_, v_c_830_);
return v___x_831_;
}
else
{
lean_object* v_val_832_; lean_object* v___x_833_; lean_object* v_c_834_; lean_object* v___x_835_; 
v_val_832_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_val_832_);
lean_dec_ref(v___x_828_);
v___x_833_ = lean_unsigned_to_nat(1u);
v_c_834_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v_keys_821_, v_v_822_, v___x_833_, v_val_832_);
lean_inc(v_k_827_);
v___x_835_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(v_d_820_, v_k_827_, v_c_834_);
return v___x_835_;
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v_v_822_);
lean_dec_ref(v_d_820_);
v___x_836_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3);
v___x_837_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__3(v___x_836_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_838_, lean_object* v_keys_839_, lean_object* v_v_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_d_838_, v_keys_839_, v_v_840_);
lean_dec_ref(v_keys_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_842_, lean_object* v_thm_843_){
_start:
{
lean_object* v_tree_844_; lean_object* v_erased_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_856_; 
v_tree_844_ = lean_ctor_get(v_x_842_, 0);
v_erased_845_ = lean_ctor_get(v_x_842_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_856_ == 0)
{
v___x_847_ = v_x_842_;
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_erased_845_);
lean_inc(v_tree_844_);
lean_dec(v_x_842_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_declName_849_; lean_object* v_keys_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v_declName_849_ = lean_ctor_get(v_thm_843_, 0);
lean_inc(v_declName_849_);
v_keys_850_ = lean_ctor_get(v_thm_843_, 2);
lean_inc_ref(v_keys_850_);
v___x_851_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_tree_844_, v_keys_850_, v_thm_843_);
lean_dec_ref(v_keys_850_);
v___x_852_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_erased_845_, v_declName_849_);
lean_dec(v_declName_849_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_852_);
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_854_ = v___x_847_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v___y_857_){
_start:
{
lean_inc_ref(v___y_857_);
return v___y_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v___y_858_);
lean_dec_ref(v___y_858_);
return v_res_859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___f_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___f_873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_874_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__3);
v___f_875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___f_875_);
lean_ctor_set(v___x_877_, 2, v___x_874_);
lean_ctor_set(v___x_877_, 3, v___f_873_);
lean_ctor_set(v___x_877_, 4, v___f_872_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_);
v___x_880_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_884_, v_x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(v_00_u03b2_887_, v_x_888_, v_x_889_);
lean_dec(v_x_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_892_, v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_895_, v_x_896_, v_x_897_);
lean_dec(v_x_897_);
lean_dec_ref(v_x_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_900_, v_x_901_, v_x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, size_t v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg(v_x_905_, v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___boxed(lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
size_t v_x_2683__boxed_913_; lean_object* v_res_914_; 
v_x_2683__boxed_913_ = lean_unbox_usize(v_x_911_);
lean_dec(v_x_911_);
v_res_914_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5(v_00_u03b2_909_, v_x_910_, v_x_2683__boxed_913_, v_x_912_);
lean_dec(v_x_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, size_t v_x_917_, lean_object* v_x_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_916_, v_x_917_, v_x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
size_t v_x_2694__boxed_924_; lean_object* v_res_925_; 
v_x_2694__boxed_924_ = lean_unbox_usize(v_x_922_);
lean_dec(v_x_922_);
v_res_925_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_920_, v_x_921_, v_x_2694__boxed_924_, v_x_923_);
lean_dec(v_x_923_);
lean_dec_ref(v_x_921_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_00_u03b2_926_, lean_object* v_x_927_, size_t v_x_928_, size_t v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_927_, v_x_928_, v_x_929_, v_x_930_, v_x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
size_t v_x_2705__boxed_939_; size_t v_x_2706__boxed_940_; lean_object* v_res_941_; 
v_x_2705__boxed_939_ = lean_unbox_usize(v_x_935_);
lean_dec(v_x_935_);
v_x_2706__boxed_940_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_res_941_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_933_, v_x_934_, v_x_2705__boxed_939_, v_x_2706__boxed_940_, v_x_937_, v_x_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_942_, lean_object* v_keys_943_, lean_object* v_vals_944_, lean_object* v_heq_945_, lean_object* v_i_946_, lean_object* v_k_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_keys_943_, v_vals_944_, v_i_946_, v_k_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_949_, lean_object* v_keys_950_, lean_object* v_vals_951_, lean_object* v_heq_952_, lean_object* v_i_953_, lean_object* v_k_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b2_949_, v_keys_950_, v_vals_951_, v_heq_952_, v_i_953_, v_k_954_);
lean_dec(v_k_954_);
lean_dec_ref(v_vals_951_);
lean_dec_ref(v_keys_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_956_, lean_object* v_n_957_, lean_object* v_k_958_, lean_object* v_v_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_n_957_, v_k_958_, v_v_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_961_, size_t v_depth_962_, lean_object* v_keys_963_, lean_object* v_vals_964_, lean_object* v_heq_965_, lean_object* v_i_966_, lean_object* v_entries_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___redArg(v_depth_962_, v_keys_963_, v_vals_964_, v_i_966_, v_entries_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_969_, lean_object* v_depth_970_, lean_object* v_keys_971_, lean_object* v_vals_972_, lean_object* v_heq_973_, lean_object* v_i_974_, lean_object* v_entries_975_){
_start:
{
size_t v_depth_boxed_976_; lean_object* v_res_977_; 
v_depth_boxed_976_ = lean_unbox_usize(v_depth_970_);
lean_dec(v_depth_970_);
v_res_977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__8(v_00_u03b2_969_, v_depth_boxed_976_, v_keys_971_, v_vals_972_, v_heq_973_, v_i_974_, v_entries_975_);
lean_dec_ref(v_vals_972_);
lean_dec_ref(v_keys_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13(lean_object* v_x_978_, lean_object* v_keys_979_, lean_object* v_v_980_, lean_object* v_k_981_, lean_object* v_as_982_, lean_object* v_k_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___redArg(v_x_978_, v_keys_979_, v_v_980_, v_k_981_, v_as_982_, v_k_983_, v_x_984_, v_x_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13___boxed(lean_object* v_x_989_, lean_object* v_keys_990_, lean_object* v_v_991_, lean_object* v_k_992_, lean_object* v_as_993_, lean_object* v_k_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2_spec__6_spec__13(v_x_989_, v_keys_990_, v_v_991_, v_k_992_, v_as_993_, v_k_994_, v_x_995_, v_x_996_, v_x_997_, v_x_998_);
lean_dec_ref(v_k_994_);
lean_dec_ref(v_keys_990_);
lean_dec(v_x_989_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10(lean_object* v_00_u03b2_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_x_1001_, v_x_1002_, v_x_1003_, v_x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_getExtTheorems___lam__0(lean_object* v_x1_1006_, lean_object* v_x2_1007_){
_start:
{
lean_object* v_priority_1008_; lean_object* v_priority_1009_; uint8_t v___x_1010_; 
v_priority_1008_ = lean_ctor_get(v_x1_1006_, 1);
v_priority_1009_ = lean_ctor_get(v_x2_1007_, 1);
v___x_1010_ = lean_nat_dec_lt(v_priority_1008_, v_priority_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(lean_object* v_x1_1011_, lean_object* v_x2_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Lean_Meta_Ext_getExtTheorems___lam__0(v_x1_1011_, v_x2_1012_);
lean_dec_ref(v_x2_1012_);
lean_dec_ref(v_x1_1011_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__1(lean_object* v___x_1015_, lean_object* v___x_1016_, lean_object* v___x_1017_, lean_object* v_x1_1018_, lean_object* v_x2_1019_){
_start:
{
lean_object* v_erased_1020_; lean_object* v_declName_1021_; uint8_t v___x_1022_; 
v_erased_1020_ = lean_ctor_get(v___x_1015_, 1);
lean_inc_ref(v_erased_1020_);
lean_dec_ref(v___x_1015_);
v_declName_1021_ = lean_ctor_get(v_x2_1019_, 0);
lean_inc(v_declName_1021_);
v___x_1022_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1016_, v___x_1017_, v_erased_1020_, v_declName_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_array_push(v_x1_1018_, v_x2_1019_);
return v___x_1023_;
}
else
{
lean_dec_ref(v_x2_1019_);
return v_x1_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object* v_ty_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v_env_1053_; lean_object* v___x_1054_; lean_object* v_ext_1055_; lean_object* v_toEnvExtension_1056_; lean_object* v_asyncMode_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_tree_1060_; lean_object* v___x_1061_; 
v___x_1052_ = lean_st_ref_get(v_a_1050_);
v_env_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_env_1053_);
lean_dec(v___x_1052_);
v___x_1054_ = l_Lean_Meta_Ext_extExtension;
v_ext_1055_ = lean_ctor_get(v___x_1054_, 1);
v_toEnvExtension_1056_ = lean_ctor_get(v_ext_1055_, 0);
v_asyncMode_1057_ = lean_ctor_get(v_toEnvExtension_1056_, 2);
v___x_1058_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1059_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1058_, v___x_1054_, v_env_1053_, v_asyncMode_1057_);
v_tree_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_ref(v_tree_1060_);
v___x_1061_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_tree_1060_, v_ty_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec_ref(v_tree_1060_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1091_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1091_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1091_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___f_1066_; lean_object* v___y_1068_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___f_1066_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__0));
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_array_get_size(v_a_1062_);
v___x_1078_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0));
v___x_1079_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__10));
v___x_1080_ = lean_nat_dec_lt(v___x_1076_, v___x_1077_);
if (v___x_1080_ == 0)
{
lean_dec(v_a_1062_);
lean_dec(v___x_1059_);
v___y_1068_ = v___x_1078_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; uint8_t v___x_1084_; 
v___x_1081_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__11));
v___x_1082_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__12));
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_getExtTheorems___lam__1), 5, 3);
lean_closure_set(v___f_1083_, 0, v___x_1059_);
lean_closure_set(v___f_1083_, 1, v___x_1081_);
lean_closure_set(v___f_1083_, 2, v___x_1082_);
v___x_1084_ = lean_nat_dec_le(v___x_1077_, v___x_1077_);
if (v___x_1084_ == 0)
{
if (v___x_1080_ == 0)
{
lean_dec_ref(v___f_1083_);
lean_dec(v_a_1062_);
v___y_1068_ = v___x_1078_;
goto v___jp_1067_;
}
else
{
size_t v___x_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = lean_usize_of_nat(v___x_1077_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1079_, v___f_1083_, v_a_1062_, v___x_1085_, v___x_1086_, v___x_1078_);
v___y_1068_ = v___x_1087_;
goto v___jp_1067_;
}
}
else
{
size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_of_nat(v___x_1077_);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1079_, v___f_1083_, v_a_1062_, v___x_1088_, v___x_1089_, v___x_1078_);
v___y_1068_ = v___x_1090_;
goto v___jp_1067_;
}
}
v___jp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_array_get_size(v___y_1068_);
v___x_1071_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(lean_box(0), v___f_1066_, v___y_1068_, v___x_1069_, v___x_1070_);
v___x_1072_ = l_Array_reverse___redArg(v___x_1071_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1072_);
v___x_1074_ = v___x_1064_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_dec(v___x_1059_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___boxed(lean_object* v_ty_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Meta_Ext_getExtTheorems(v_ty_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_ks_1103_; lean_object* v_vs_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1128_; 
v_ks_1103_ = lean_ctor_get(v_x_1099_, 0);
v_vs_1104_ = lean_ctor_get(v_x_1099_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1099_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1106_ = v_x_1099_;
v_isShared_1107_ = v_isSharedCheck_1128_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_vs_1104_);
lean_inc(v_ks_1103_);
lean_dec(v_x_1099_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1128_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = lean_array_get_size(v_ks_1103_);
v___x_1109_ = lean_nat_dec_lt(v_x_1100_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
lean_dec(v_x_1100_);
v___x_1110_ = lean_array_push(v_ks_1103_, v_x_1101_);
v___x_1111_ = lean_array_push(v_vs_1104_, v_x_1102_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1111_);
lean_ctor_set(v___x_1106_, 0, v___x_1110_);
v___x_1113_ = v___x_1106_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
else
{
lean_object* v_k_x27_1115_; uint8_t v___x_1116_; 
v_k_x27_1115_ = lean_array_fget_borrowed(v_ks_1103_, v_x_1100_);
v___x_1116_ = lean_name_eq(v_x_1101_, v_k_x27_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1118_; 
if (v_isShared_1107_ == 0)
{
v___x_1118_ = v___x_1106_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_ks_1103_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_vs_1104_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = lean_nat_add(v_x_1100_, v___x_1119_);
lean_dec(v_x_1100_);
v_x_1099_ = v___x_1118_;
v_x_1100_ = v___x_1120_;
goto _start;
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1123_ = lean_array_fset(v_ks_1103_, v_x_1100_, v_x_1101_);
v___x_1124_ = lean_array_fset(v_vs_1104_, v_x_1100_, v_x_1102_);
lean_dec(v_x_1100_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1124_);
lean_ctor_set(v___x_1106_, 0, v___x_1123_);
v___x_1126_ = v___x_1106_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1129_, lean_object* v_k_1130_, lean_object* v_v_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1129_, v___x_1132_, v_k_1130_, v_v_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(lean_object* v_x_1135_, size_t v_x_1136_, size_t v_x_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1135_) == 0)
{
lean_object* v_es_1140_; size_t v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; lean_object* v_j_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_es_1140_ = lean_ctor_get(v_x_1135_, 0);
v___x_1141_ = ((size_t)5ULL);
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
v___x_1144_ = lean_usize_land(v_x_1136_, v___x_1143_);
v_j_1145_ = lean_usize_to_nat(v___x_1144_);
v___x_1146_ = lean_array_get_size(v_es_1140_);
v___x_1147_ = lean_nat_dec_lt(v_j_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_dec(v_j_1145_);
lean_dec(v_x_1139_);
lean_dec(v_x_1138_);
return v_x_1135_;
}
else
{
lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1184_; 
lean_inc_ref(v_es_1140_);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_x_1135_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v_x_1135_, 0);
lean_dec(v_unused_1185_);
v___x_1149_ = v_x_1135_;
v_isShared_1150_ = v_isSharedCheck_1184_;
goto v_resetjp_1148_;
}
else
{
lean_dec(v_x_1135_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1184_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_v_1151_; lean_object* v___x_1152_; lean_object* v_xs_x27_1153_; lean_object* v___y_1155_; 
v_v_1151_ = lean_array_fget(v_es_1140_, v_j_1145_);
v___x_1152_ = lean_box(0);
v_xs_x27_1153_ = lean_array_fset(v_es_1140_, v_j_1145_, v___x_1152_);
switch(lean_obj_tag(v_v_1151_))
{
case 0:
{
lean_object* v_key_1160_; lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1171_; 
v_key_1160_ = lean_ctor_get(v_v_1151_, 0);
v_val_1161_ = lean_ctor_get(v_v_1151_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_v_1151_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1163_ = v_v_1151_;
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_inc(v_key_1160_);
lean_dec(v_v_1151_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_name_eq(v_x_1138_, v_key_1160_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_del_object(v___x_1163_);
v___x_1166_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1160_, v_val_1161_, v_x_1138_, v_x_1139_);
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
v___y_1155_ = v___x_1167_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1169_; 
lean_dec(v_val_1161_);
lean_dec(v_key_1160_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v_x_1139_);
lean_ctor_set(v___x_1163_, 0, v_x_1138_);
v___x_1169_ = v___x_1163_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_x_1138_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_x_1139_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
v___y_1155_ = v___x_1169_;
goto v___jp_1154_;
}
}
}
}
case 1:
{
lean_object* v_node_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1182_; 
v_node_1172_ = lean_ctor_get(v_v_1151_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_v_1151_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1174_ = v_v_1151_;
v_isShared_1175_ = v_isSharedCheck_1182_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_node_1172_);
lean_dec(v_v_1151_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1182_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
size_t v___x_1176_; size_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1176_ = lean_usize_shift_right(v_x_1136_, v___x_1141_);
v___x_1177_ = lean_usize_add(v_x_1137_, v___x_1142_);
v___x_1178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_node_1172_, v___x_1176_, v___x_1177_, v_x_1138_, v_x_1139_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1178_);
v___x_1180_ = v___x_1174_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
v___y_1155_ = v___x_1180_;
goto v___jp_1154_;
}
}
}
default: 
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_x_1138_);
lean_ctor_set(v___x_1183_, 1, v_x_1139_);
v___y_1155_ = v___x_1183_;
goto v___jp_1154_;
}
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_array_fset(v_xs_x27_1153_, v_j_1145_, v___y_1155_);
lean_dec(v_j_1145_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1156_);
v___x_1158_ = v___x_1149_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
else
{
lean_object* v_ks_1186_; lean_object* v_vs_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1207_; 
v_ks_1186_ = lean_ctor_get(v_x_1135_, 0);
v_vs_1187_ = lean_ctor_get(v_x_1135_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_x_1135_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1189_ = v_x_1135_;
v_isShared_1190_ = v_isSharedCheck_1207_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_vs_1187_);
lean_inc(v_ks_1186_);
lean_dec(v_x_1135_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1207_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_ks_1186_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_vs_1187_);
v___x_1192_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v_newNode_1193_; uint8_t v___y_1195_; size_t v___x_1201_; uint8_t v___x_1202_; 
v_newNode_1193_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v___x_1192_, v_x_1138_, v_x_1139_);
v___x_1201_ = ((size_t)7ULL);
v___x_1202_ = lean_usize_dec_le(v___x_1201_, v_x_1137_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1203_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1193_);
v___x_1204_ = lean_unsigned_to_nat(4u);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
lean_dec(v___x_1203_);
v___y_1195_ = v___x_1205_;
goto v___jp_1194_;
}
else
{
v___y_1195_ = v___x_1202_;
goto v___jp_1194_;
}
v___jp_1194_:
{
if (v___y_1195_ == 0)
{
lean_object* v_ks_1196_; lean_object* v_vs_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_ks_1196_ = lean_ctor_get(v_newNode_1193_, 0);
lean_inc_ref(v_ks_1196_);
v_vs_1197_ = lean_ctor_get(v_newNode_1193_, 1);
lean_inc_ref(v_vs_1197_);
lean_dec_ref(v_newNode_1193_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___closed__0);
v___x_1200_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_x_1137_, v_ks_1196_, v_vs_1197_, v___x_1198_, v___x_1199_);
lean_dec_ref(v_vs_1197_);
lean_dec_ref(v_ks_1196_);
return v___x_1200_;
}
else
{
return v_newNode_1193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_1208_, lean_object* v_keys_1209_, lean_object* v_vals_1210_, lean_object* v_i_1211_, lean_object* v_entries_1212_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_array_get_size(v_keys_1209_);
v___x_1214_ = lean_nat_dec_lt(v_i_1211_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec(v_i_1211_);
return v_entries_1212_;
}
else
{
lean_object* v_k_1215_; lean_object* v_v_1216_; uint64_t v___y_1218_; 
v_k_1215_ = lean_array_fget_borrowed(v_keys_1209_, v_i_1211_);
v_v_1216_ = lean_array_fget_borrowed(v_vals_1210_, v_i_1211_);
if (lean_obj_tag(v_k_1215_) == 0)
{
uint64_t v___x_1229_; 
v___x_1229_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1218_ = v___x_1229_;
goto v___jp_1217_;
}
else
{
uint64_t v_hash_1230_; 
v_hash_1230_ = lean_ctor_get_uint64(v_k_1215_, sizeof(void*)*2);
v___y_1218_ = v_hash_1230_;
goto v___jp_1217_;
}
v___jp_1217_:
{
size_t v_h_1219_; size_t v___x_1220_; lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; size_t v_h_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_h_1219_ = lean_uint64_to_usize(v___y_1218_);
v___x_1220_ = ((size_t)5ULL);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_sub(v_depth_1208_, v___x_1222_);
v___x_1224_ = lean_usize_mul(v___x_1220_, v___x_1223_);
v_h_1225_ = lean_usize_shift_right(v_h_1219_, v___x_1224_);
v___x_1226_ = lean_nat_add(v_i_1211_, v___x_1221_);
lean_dec(v_i_1211_);
lean_inc(v_v_1216_);
lean_inc(v_k_1215_);
v___x_1227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_entries_1212_, v_h_1225_, v_depth_1208_, v_k_1215_, v_v_1216_);
v_i_1211_ = v___x_1226_;
v_entries_1212_ = v___x_1227_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1231_, lean_object* v_keys_1232_, lean_object* v_vals_1233_, lean_object* v_i_1234_, lean_object* v_entries_1235_){
_start:
{
size_t v_depth_boxed_1236_; lean_object* v_res_1237_; 
v_depth_boxed_1236_ = lean_unbox_usize(v_depth_1231_);
lean_dec(v_depth_1231_);
v_res_1237_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1236_, v_keys_1232_, v_vals_1233_, v_i_1234_, v_entries_1235_);
lean_dec_ref(v_vals_1233_);
lean_dec_ref(v_keys_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
size_t v_x_371__boxed_1243_; size_t v_x_372__boxed_1244_; lean_object* v_res_1245_; 
v_x_371__boxed_1243_ = lean_unbox_usize(v_x_1239_);
lean_dec(v_x_1239_);
v_x_372__boxed_1244_ = lean_unbox_usize(v_x_1240_);
lean_dec(v_x_1240_);
v_res_1245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1238_, v_x_371__boxed_1243_, v_x_372__boxed_1244_, v_x_1241_, v_x_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(lean_object* v_x_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint64_t v___y_1250_; 
if (lean_obj_tag(v_x_1247_) == 0)
{
uint64_t v___x_1254_; 
v___x_1254_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1250_ = v___x_1254_;
goto v___jp_1249_;
}
else
{
uint64_t v_hash_1255_; 
v_hash_1255_ = lean_ctor_get_uint64(v_x_1247_, sizeof(void*)*2);
v___y_1250_ = v_hash_1255_;
goto v___jp_1249_;
}
v___jp_1249_:
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_uint64_to_usize(v___y_1250_);
v___x_1252_ = ((size_t)1ULL);
v___x_1253_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1246_, v___x_1251_, v___x_1252_, v_x_1247_, v_x_1248_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object* v_d_1256_, lean_object* v_declName_1257_){
_start:
{
lean_object* v_tree_1258_; lean_object* v_erased_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
v_tree_1258_ = lean_ctor_get(v_d_1256_, 0);
v_erased_1259_ = lean_ctor_get(v_d_1256_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_d_1256_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1261_ = v_d_1256_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_erased_1259_);
lean_inc(v_tree_1258_);
lean_dec(v_d_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_erased_1259_, v_declName_1257_, v___x_1263_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1264_);
v___x_1266_ = v___x_1261_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_tree_1258_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0(lean_object* v_00_u03b2_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_x_1270_, v_x_1271_, v_x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(lean_object* v_00_u03b2_1274_, lean_object* v_x_1275_, size_t v_x_1276_, size_t v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1275_, v_x_1276_, v_x_1277_, v_x_1278_, v_x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
size_t v_x_576__boxed_1287_; size_t v_x_577__boxed_1288_; lean_object* v_res_1289_; 
v_x_576__boxed_1287_ = lean_unbox_usize(v_x_1283_);
lean_dec(v_x_1283_);
v_x_577__boxed_1288_ = lean_unbox_usize(v_x_1284_);
lean_dec(v_x_1284_);
v_res_1289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(v_00_u03b2_1281_, v_x_1282_, v_x_576__boxed_1287_, v_x_577__boxed_1288_, v_x_1285_, v_x_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1290_, lean_object* v_n_1291_, lean_object* v_k_1292_, lean_object* v_v_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v_n_1291_, v_k_1292_, v_v_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1295_, size_t v_depth_1296_, lean_object* v_keys_1297_, lean_object* v_vals_1298_, lean_object* v_heq_1299_, lean_object* v_i_1300_, lean_object* v_entries_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_1296_, v_keys_1297_, v_vals_1298_, v_i_1300_, v_entries_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1303_, lean_object* v_depth_1304_, lean_object* v_keys_1305_, lean_object* v_vals_1306_, lean_object* v_heq_1307_, lean_object* v_i_1308_, lean_object* v_entries_1309_){
_start:
{
size_t v_depth_boxed_1310_; lean_object* v_res_1311_; 
v_depth_boxed_1310_ = lean_unbox_usize(v_depth_1304_);
lean_dec(v_depth_1304_);
v_res_1311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(v_00_u03b2_1303_, v_depth_boxed_1310_, v_keys_1305_, v_vals_1306_, v_heq_1307_, v_i_1308_, v_entries_1309_);
lean_dec_ref(v_vals_1306_);
lean_dec_ref(v_keys_1305_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1313_, v_x_1314_, v_x_1315_, v_x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(lean_object* v_declName_1318_, uint8_t v_x1_1319_, lean_object* v_x2_1320_){
_start:
{
if (v_x1_1319_ == 0)
{
lean_object* v_declName_1321_; uint8_t v___x_1322_; 
v_declName_1321_ = lean_ctor_get(v_x2_1320_, 0);
v___x_1322_ = lean_name_eq(v_declName_1321_, v_declName_1318_);
return v___x_1322_;
}
else
{
return v_x1_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(lean_object* v_declName_1323_, lean_object* v_x1_1324_, lean_object* v_x2_1325_){
_start:
{
uint8_t v_x1_1199__boxed_1326_; uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_x1_1199__boxed_1326_ = lean_unbox(v_x1_1324_);
v_res_1327_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(v_declName_1323_, v_x1_1199__boxed_1326_, v_x2_1325_);
lean_dec_ref(v_x2_1325_);
lean_dec(v_declName_1323_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(lean_object* v_f_1329_, lean_object* v_as_1330_, size_t v_i_1331_, size_t v_stop_1332_, lean_object* v_b_1333_){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_usize_dec_eq(v_i_1331_, v_stop_1332_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; 
v___x_1335_ = lean_array_uget_borrowed(v_as_1330_, v_i_1331_);
lean_inc(v_f_1329_);
lean_inc(v___x_1335_);
v___x_1336_ = lean_apply_2(v_f_1329_, v_b_1333_, v___x_1335_);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1331_, v___x_1337_);
v_i_1331_ = v___x_1338_;
v_b_1333_ = v___x_1336_;
goto _start;
}
else
{
lean_dec(v_f_1329_);
return v_b_1333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg___boxed(lean_object* v_f_1340_, lean_object* v_as_1341_, lean_object* v_i_1342_, lean_object* v_stop_1343_, lean_object* v_b_1344_){
_start:
{
size_t v_i_boxed_1345_; size_t v_stop_boxed_1346_; lean_object* v_res_1347_; 
v_i_boxed_1345_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_stop_boxed_1346_ = lean_unbox_usize(v_stop_1343_);
lean_dec(v_stop_1343_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1340_, v_as_1341_, v_i_boxed_1345_, v_stop_boxed_1346_, v_b_1344_);
lean_dec_ref(v_as_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(lean_object* v_f_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v_vs_1351_; lean_object* v_children_1352_; lean_object* v___x_1353_; lean_object* v_s_1355_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_vs_1351_ = lean_ctor_get(v_x_1350_, 0);
v_children_1352_ = lean_ctor_get(v_x_1350_, 1);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_array_get_size(v_vs_1351_);
v___x_1366_ = lean_nat_dec_lt(v___x_1353_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_children_1352_);
v___x_1368_ = lean_nat_dec_lt(v___x_1353_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v_f_1348_);
return v_x_1349_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_nat_dec_le(v___x_1367_, v___x_1367_);
if (v___x_1369_ == 0)
{
if (v___x_1368_ == 0)
{
lean_dec(v_f_1348_);
return v_x_1349_;
}
else
{
size_t v___x_1370_; size_t v___x_1371_; lean_object* v___x_1372_; 
v___x_1370_ = ((size_t)0ULL);
v___x_1371_ = lean_usize_of_nat(v___x_1367_);
v___x_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1348_, v_children_1352_, v___x_1370_, v___x_1371_, v_x_1349_);
return v___x_1372_;
}
}
else
{
size_t v___x_1373_; size_t v___x_1374_; lean_object* v___x_1375_; 
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = lean_usize_of_nat(v___x_1367_);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1348_, v_children_1352_, v___x_1373_, v___x_1374_, v_x_1349_);
return v___x_1375_;
}
}
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_nat_dec_le(v___x_1365_, v___x_1365_);
if (v___x_1376_ == 0)
{
if (v___x_1366_ == 0)
{
v_s_1355_ = v_x_1349_;
goto v___jp_1354_;
}
else
{
size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = lean_usize_of_nat(v___x_1365_);
lean_inc(v_f_1348_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1348_, v_vs_1351_, v___x_1377_, v___x_1378_, v_x_1349_);
v_s_1355_ = v___x_1379_;
goto v___jp_1354_;
}
}
else
{
size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = lean_usize_of_nat(v___x_1365_);
lean_inc(v_f_1348_);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1348_, v_vs_1351_, v___x_1380_, v___x_1381_, v_x_1349_);
v_s_1355_ = v___x_1382_;
goto v___jp_1354_;
}
}
v___jp_1354_:
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = lean_array_get_size(v_children_1352_);
v___x_1357_ = lean_nat_dec_lt(v___x_1353_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec(v_f_1348_);
return v_s_1355_;
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_nat_dec_le(v___x_1356_, v___x_1356_);
if (v___x_1358_ == 0)
{
if (v___x_1357_ == 0)
{
lean_dec(v_f_1348_);
return v_s_1355_;
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1356_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1348_, v_children_1352_, v___x_1359_, v___x_1360_, v_s_1355_);
return v___x_1361_;
}
}
else
{
size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = lean_usize_of_nat(v___x_1356_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1348_, v_children_1352_, v___x_1362_, v___x_1363_, v_s_1355_);
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(lean_object* v_f_1383_, lean_object* v_as_1384_, size_t v_i_1385_, size_t v_stop_1386_, lean_object* v_b_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_usize_dec_eq(v_i_1385_, v_stop_1386_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v_snd_1390_; lean_object* v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; 
v___x_1389_ = lean_array_uget_borrowed(v_as_1384_, v_i_1385_);
v_snd_1390_ = lean_ctor_get(v___x_1389_, 1);
lean_inc(v_f_1383_);
v___x_1391_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1383_, v_b_1387_, v_snd_1390_);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_add(v_i_1385_, v___x_1392_);
v_i_1385_ = v___x_1393_;
v_b_1387_ = v___x_1391_;
goto _start;
}
else
{
lean_dec(v_f_1383_);
return v_b_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_f_1395_, lean_object* v_as_1396_, lean_object* v_i_1397_, lean_object* v_stop_1398_, lean_object* v_b_1399_){
_start:
{
size_t v_i_boxed_1400_; size_t v_stop_boxed_1401_; lean_object* v_res_1402_; 
v_i_boxed_1400_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_stop_boxed_1401_ = lean_unbox_usize(v_stop_1398_);
lean_dec(v_stop_1398_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1395_, v_as_1396_, v_i_boxed_1400_, v_stop_boxed_1401_, v_b_1399_);
lean_dec_ref(v_as_1396_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg___boxed(lean_object* v_f_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1403_, v_x_1404_, v_x_1405_);
lean_dec_ref(v_x_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(lean_object* v___f_1407_, uint8_t v_s_1408_, lean_object* v_x_1409_, lean_object* v_t_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_box(v_s_1408_);
v___x_1412_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v___f_1407_, v___x_1411_, v_t_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed(lean_object* v___f_1413_, lean_object* v_s_1414_, lean_object* v_x_1415_, lean_object* v_t_1416_){
_start:
{
uint8_t v_s_boxed_1417_; lean_object* v_res_1418_; 
v_s_boxed_1417_ = lean_unbox(v_s_1414_);
v_res_1418_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__1(v___f_1413_, v_s_boxed_1417_, v_x_1415_, v_t_1416_);
lean_dec_ref(v_t_1416_);
lean_dec(v_x_1415_);
return v_res_1418_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(lean_object* v_keys_1419_, lean_object* v_i_1420_, lean_object* v_k_1421_){
_start:
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = lean_array_get_size(v_keys_1419_);
v___x_1423_ = lean_nat_dec_lt(v_i_1420_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_dec(v_i_1420_);
return v___x_1423_;
}
else
{
lean_object* v_k_x27_1424_; uint8_t v___x_1425_; 
v_k_x27_1424_ = lean_array_fget_borrowed(v_keys_1419_, v_i_1420_);
v___x_1425_ = lean_name_eq(v_k_1421_, v_k_x27_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_unsigned_to_nat(1u);
v___x_1427_ = lean_nat_add(v_i_1420_, v___x_1426_);
lean_dec(v_i_1420_);
v_i_1420_ = v___x_1427_;
goto _start;
}
else
{
lean_dec(v_i_1420_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1429_, lean_object* v_i_1430_, lean_object* v_k_1431_){
_start:
{
uint8_t v_res_1432_; lean_object* v_r_1433_; 
v_res_1432_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1429_, v_i_1430_, v_k_1431_);
lean_dec(v_k_1431_);
lean_dec_ref(v_keys_1429_);
v_r_1433_ = lean_box(v_res_1432_);
return v_r_1433_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(lean_object* v_x_1434_, size_t v_x_1435_, lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_object* v_es_1437_; lean_object* v___x_1438_; size_t v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; lean_object* v_j_1442_; lean_object* v___x_1443_; 
v_es_1437_ = lean_ctor_get(v_x_1434_, 0);
v___x_1438_ = lean_box(2);
v___x_1439_ = ((size_t)5ULL);
v___x_1440_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__5___redArg___closed__1);
v___x_1441_ = lean_usize_land(v_x_1435_, v___x_1440_);
v_j_1442_ = lean_usize_to_nat(v___x_1441_);
v___x_1443_ = lean_array_get_borrowed(v___x_1438_, v_es_1437_, v_j_1442_);
lean_dec(v_j_1442_);
switch(lean_obj_tag(v___x_1443_))
{
case 0:
{
lean_object* v_key_1444_; uint8_t v___x_1445_; 
v_key_1444_ = lean_ctor_get(v___x_1443_, 0);
v___x_1445_ = lean_name_eq(v_x_1436_, v_key_1444_);
return v___x_1445_;
}
case 1:
{
lean_object* v_node_1446_; size_t v___x_1447_; 
v_node_1446_ = lean_ctor_get(v___x_1443_, 0);
v___x_1447_ = lean_usize_shift_right(v_x_1435_, v___x_1439_);
v_x_1434_ = v_node_1446_;
v_x_1435_ = v___x_1447_;
goto _start;
}
default: 
{
uint8_t v___x_1449_; 
v___x_1449_ = 0;
return v___x_1449_;
}
}
}
else
{
lean_object* v_ks_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_ks_1450_ = lean_ctor_get(v_x_1434_, 0);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_ks_1450_, v___x_1451_, v_x_1436_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
size_t v_x_1331__boxed_1456_; uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_x_1331__boxed_1456_ = lean_unbox_usize(v_x_1454_);
lean_dec(v_x_1454_);
v_res_1457_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1453_, v_x_1331__boxed_1456_, v_x_1455_);
lean_dec(v_x_1455_);
lean_dec_ref(v_x_1453_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
uint64_t v___y_1462_; 
if (lean_obj_tag(v_x_1460_) == 0)
{
uint64_t v___x_1465_; 
v___x_1465_ = lean_uint64_once(&l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0, &l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0_once, _init_l_Lean_Meta_Ext_instHashableExtTheorem_hash___closed__0);
v___y_1462_ = v___x_1465_;
goto v___jp_1461_;
}
else
{
uint64_t v_hash_1466_; 
v_hash_1466_ = lean_ctor_get_uint64(v_x_1460_, sizeof(void*)*2);
v___y_1462_ = v_hash_1466_;
goto v___jp_1461_;
}
v___jp_1461_:
{
size_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_uint64_to_usize(v___y_1462_);
v___x_1464_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1459_, v___x_1463_, v_x_1460_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1467_, v_x_1468_);
lean_dec(v_x_1468_);
lean_dec_ref(v_x_1467_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(lean_object* v_f_1471_, lean_object* v_keys_1472_, lean_object* v_vals_1473_, lean_object* v_i_1474_, lean_object* v_acc_1475_){
_start:
{
lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_array_get_size(v_keys_1472_);
v___x_1477_ = lean_nat_dec_lt(v_i_1474_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_dec(v_i_1474_);
lean_dec(v_f_1471_);
return v_acc_1475_;
}
else
{
lean_object* v_k_1478_; lean_object* v_v_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_k_1478_ = lean_array_fget_borrowed(v_keys_1472_, v_i_1474_);
v_v_1479_ = lean_array_fget_borrowed(v_vals_1473_, v_i_1474_);
lean_inc(v_f_1471_);
lean_inc(v_v_1479_);
lean_inc(v_k_1478_);
v___x_1480_ = lean_apply_3(v_f_1471_, v_acc_1475_, v_k_1478_, v_v_1479_);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_i_1474_, v___x_1481_);
lean_dec(v_i_1474_);
v_i_1474_ = v___x_1482_;
v_acc_1475_ = v___x_1480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_1484_, lean_object* v_keys_1485_, lean_object* v_vals_1486_, lean_object* v_i_1487_, lean_object* v_acc_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1484_, v_keys_1485_, v_vals_1486_, v_i_1487_, v_acc_1488_);
lean_dec_ref(v_vals_1486_);
lean_dec_ref(v_keys_1485_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(lean_object* v_f_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v_es_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_es_1493_ = lean_ctor_get(v_x_1491_, 0);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_array_get_size(v_es_1493_);
v___x_1496_ = lean_nat_dec_lt(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_dec(v_f_1490_);
return v_x_1492_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_nat_dec_le(v___x_1495_, v___x_1495_);
if (v___x_1497_ == 0)
{
if (v___x_1496_ == 0)
{
lean_dec(v_f_1490_);
return v_x_1492_;
}
else
{
size_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = ((size_t)0ULL);
v___x_1499_ = lean_usize_of_nat(v___x_1495_);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1490_, v_es_1493_, v___x_1498_, v___x_1499_, v_x_1492_);
return v___x_1500_;
}
}
else
{
size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = lean_usize_of_nat(v___x_1495_);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1490_, v_es_1493_, v___x_1501_, v___x_1502_, v_x_1492_);
return v___x_1503_;
}
}
}
else
{
lean_object* v_ks_1504_; lean_object* v_vs_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_ks_1504_ = lean_ctor_get(v_x_1491_, 0);
v_vs_1505_ = lean_ctor_get(v_x_1491_, 1);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1490_, v_ks_1504_, v_vs_1505_, v___x_1506_, v_x_1492_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1508_, lean_object* v_as_1509_, size_t v_i_1510_, size_t v_stop_1511_, lean_object* v_b_1512_){
_start:
{
lean_object* v___y_1514_; uint8_t v___x_1518_; 
v___x_1518_ = lean_usize_dec_eq(v_i_1510_, v_stop_1511_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_array_uget_borrowed(v_as_1509_, v_i_1510_);
switch(lean_obj_tag(v___x_1519_))
{
case 0:
{
lean_object* v_key_1520_; lean_object* v_val_1521_; lean_object* v___x_1522_; 
v_key_1520_ = lean_ctor_get(v___x_1519_, 0);
v_val_1521_ = lean_ctor_get(v___x_1519_, 1);
lean_inc(v_f_1508_);
lean_inc(v_val_1521_);
lean_inc(v_key_1520_);
v___x_1522_ = lean_apply_3(v_f_1508_, v_b_1512_, v_key_1520_, v_val_1521_);
v___y_1514_ = v___x_1522_;
goto v___jp_1513_;
}
case 1:
{
lean_object* v_node_1523_; lean_object* v___x_1524_; 
v_node_1523_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_f_1508_);
v___x_1524_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1508_, v_node_1523_, v_b_1512_);
v___y_1514_ = v___x_1524_;
goto v___jp_1513_;
}
default: 
{
v___y_1514_ = v_b_1512_;
goto v___jp_1513_;
}
}
}
else
{
lean_dec(v_f_1508_);
return v_b_1512_;
}
v___jp_1513_:
{
size_t v___x_1515_; size_t v___x_1516_; 
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_add(v_i_1510_, v___x_1515_);
v_i_1510_ = v___x_1516_;
v_b_1512_ = v___y_1514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1525_, lean_object* v_as_1526_, lean_object* v_i_1527_, lean_object* v_stop_1528_, lean_object* v_b_1529_){
_start:
{
size_t v_i_boxed_1530_; size_t v_stop_boxed_1531_; lean_object* v_res_1532_; 
v_i_boxed_1530_ = lean_unbox_usize(v_i_1527_);
lean_dec(v_i_1527_);
v_stop_boxed_1531_ = lean_unbox_usize(v_stop_1528_);
lean_dec(v_stop_1528_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1525_, v_as_1526_, v_i_boxed_1530_, v_stop_boxed_1531_, v_b_1529_);
lean_dec_ref(v_as_1526_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(lean_object* v_f_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1533_, v_x_1534_, v_x_1535_);
lean_dec_ref(v_x_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object* v_d_1537_, lean_object* v_declName_1538_){
_start:
{
lean_object* v_tree_1539_; lean_object* v_erased_1540_; lean_object* v___f_1541_; lean_object* v___f_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_tree_1539_ = lean_ctor_get(v_d_1537_, 0);
v_erased_1540_ = lean_ctor_get(v_d_1537_, 1);
lean_inc(v_declName_1538_);
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1541_, 0, v_declName_1538_);
v___f_1542_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1542_, 0, v___f_1541_);
v___x_1543_ = 0;
v___x_1544_ = lean_box(v___x_1543_);
v___x_1545_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v___f_1542_, v_tree_1539_, v___x_1544_);
v___x_1546_ = lean_unbox(v___x_1545_);
if (v___x_1546_ == 0)
{
uint8_t v___x_1547_; 
lean_dec(v_declName_1538_);
v___x_1547_ = lean_unbox(v___x_1545_);
lean_dec(v___x_1545_);
return v___x_1547_;
}
else
{
uint8_t v___x_1548_; 
v___x_1548_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_erased_1540_, v_declName_1538_);
lean_dec(v_declName_1538_);
if (v___x_1548_ == 0)
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_unbox(v___x_1545_);
lean_dec(v___x_1545_);
return v___x_1549_;
}
else
{
lean_dec(v___x_1545_);
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object* v_d_1550_, lean_object* v_declName_1551_){
_start:
{
uint8_t v_res_1552_; lean_object* v_r_1553_; 
v_res_1552_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1550_, v_declName_1551_);
lean_dec_ref(v_d_1550_);
v_r_1553_ = lean_box(v_res_1552_);
return v_r_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(lean_object* v_00_u03c3_1554_, lean_object* v_00_u03b1_1555_, lean_object* v_f_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___redArg(v_f_1556_, v_x_1557_, v_x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(lean_object* v_00_u03c3_1560_, lean_object* v_00_u03b1_1561_, lean_object* v_f_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(v_00_u03c3_1560_, v_00_u03b1_1561_, v_f_1562_, v_x_1563_, v_x_1564_);
lean_dec_ref(v_x_1564_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(lean_object* v_map_1566_, lean_object* v_f_1567_, lean_object* v_init_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1567_, v_map_1566_, v_init_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(lean_object* v_map_1570_, lean_object* v_f_1571_, lean_object* v_init_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(v_map_1570_, v_f_1571_, v_init_1572_);
lean_dec_ref(v_map_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(lean_object* v_00_u03c3_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_map_1576_, lean_object* v_f_1577_, lean_object* v_init_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1577_, v_map_1576_, v_init_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(lean_object* v_00_u03c3_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_map_1582_, lean_object* v_f_1583_, lean_object* v_init_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(v_00_u03c3_1580_, v_00_u03b2_1581_, v_map_1582_, v_f_1583_, v_init_1584_);
lean_dec_ref(v_map_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(lean_object* v_00_u03b2_1586_, lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
uint8_t v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1587_, v_x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(lean_object* v_00_u03b2_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_){
_start:
{
uint8_t v_res_1593_; lean_object* v_r_1594_; 
v_res_1593_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(v_00_u03b2_1590_, v_x_1591_, v_x_1592_);
lean_dec(v_x_1592_);
lean_dec_ref(v_x_1591_);
v_r_1594_ = lean_box(v_res_1593_);
return v_r_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03c3_1596_, lean_object* v_f_1597_, lean_object* v_as_1598_, size_t v_i_1599_, size_t v_stop_1600_, lean_object* v_b_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___redArg(v_f_1597_, v_as_1598_, v_i_1599_, v_stop_1600_, v_b_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1603_, lean_object* v_00_u03c3_1604_, lean_object* v_f_1605_, lean_object* v_as_1606_, lean_object* v_i_1607_, lean_object* v_stop_1608_, lean_object* v_b_1609_){
_start:
{
size_t v_i_boxed_1610_; size_t v_stop_boxed_1611_; lean_object* v_res_1612_; 
v_i_boxed_1610_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v_stop_boxed_1611_ = lean_unbox_usize(v_stop_1608_);
lean_dec(v_stop_1608_);
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_00_u03b1_1603_, v_00_u03c3_1604_, v_f_1605_, v_as_1606_, v_i_boxed_1610_, v_stop_boxed_1611_, v_b_1609_);
lean_dec_ref(v_as_1606_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(lean_object* v_00_u03b1_1613_, lean_object* v_00_u03c3_1614_, lean_object* v_f_1615_, lean_object* v_as_1616_, size_t v_i_1617_, size_t v_stop_1618_, lean_object* v_b_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___redArg(v_f_1615_, v_as_1616_, v_i_1617_, v_stop_1618_, v_b_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1621_, lean_object* v_00_u03c3_1622_, lean_object* v_f_1623_, lean_object* v_as_1624_, lean_object* v_i_1625_, lean_object* v_stop_1626_, lean_object* v_b_1627_){
_start:
{
size_t v_i_boxed_1628_; size_t v_stop_boxed_1629_; lean_object* v_res_1630_; 
v_i_boxed_1628_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_stop_boxed_1629_ = lean_unbox_usize(v_stop_1626_);
lean_dec(v_stop_1626_);
v_res_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(v_00_u03b1_1621_, v_00_u03c3_1622_, v_f_1623_, v_as_1624_, v_i_boxed_1628_, v_stop_boxed_1629_, v_b_1627_);
lean_dec_ref(v_as_1624_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(lean_object* v_00_u03c3_1631_, lean_object* v_00_u03b1_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_f_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1634_, v_x_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1638_, lean_object* v_00_u03b1_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_f_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(v_00_u03c3_1638_, v_00_u03b1_1639_, v_00_u03b2_1640_, v_f_1641_, v_x_1642_, v_x_1643_);
lean_dec_ref(v_x_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(lean_object* v_00_u03b2_1645_, lean_object* v_x_1646_, size_t v_x_1647_, lean_object* v_x_1648_){
_start:
{
uint8_t v___x_1649_; 
v___x_1649_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1646_, v_x_1647_, v_x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
size_t v_x_1515__boxed_1654_; uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_x_1515__boxed_1654_ = lean_unbox_usize(v_x_1652_);
lean_dec(v_x_1652_);
v_res_1655_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(v_00_u03b2_1650_, v_x_1651_, v_x_1515__boxed_1654_, v_x_1653_);
lean_dec(v_x_1653_);
lean_dec_ref(v_x_1651_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1657_, lean_object* v_00_u03b2_1658_, lean_object* v_00_u03c3_1659_, lean_object* v_f_1660_, lean_object* v_as_1661_, size_t v_i_1662_, size_t v_stop_1663_, lean_object* v_b_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1660_, v_as_1661_, v_i_1662_, v_stop_1663_, v_b_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_00_u03c3_1668_, lean_object* v_f_1669_, lean_object* v_as_1670_, lean_object* v_i_1671_, lean_object* v_stop_1672_, lean_object* v_b_1673_){
_start:
{
size_t v_i_boxed_1674_; size_t v_stop_boxed_1675_; lean_object* v_res_1676_; 
v_i_boxed_1674_ = lean_unbox_usize(v_i_1671_);
lean_dec(v_i_1671_);
v_stop_boxed_1675_ = lean_unbox_usize(v_stop_1672_);
lean_dec(v_stop_1672_);
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(v_00_u03b1_1666_, v_00_u03b2_1667_, v_00_u03c3_1668_, v_f_1669_, v_as_1670_, v_i_boxed_1674_, v_stop_boxed_1675_, v_b_1673_);
lean_dec_ref(v_as_1670_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1677_, lean_object* v_00_u03b1_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_f_1680_, lean_object* v_keys_1681_, lean_object* v_vals_1682_, lean_object* v_heq_1683_, lean_object* v_i_1684_, lean_object* v_acc_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1680_, v_keys_1681_, v_vals_1682_, v_i_1684_, v_acc_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1687_, lean_object* v_00_u03b1_1688_, lean_object* v_00_u03b2_1689_, lean_object* v_f_1690_, lean_object* v_keys_1691_, lean_object* v_vals_1692_, lean_object* v_heq_1693_, lean_object* v_i_1694_, lean_object* v_acc_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(v_00_u03c3_1687_, v_00_u03b1_1688_, v_00_u03b2_1689_, v_f_1690_, v_keys_1691_, v_vals_1692_, v_heq_1693_, v_i_1694_, v_acc_1695_);
lean_dec_ref(v_vals_1692_);
lean_dec_ref(v_keys_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1697_, lean_object* v_keys_1698_, lean_object* v_vals_1699_, lean_object* v_heq_1700_, lean_object* v_i_1701_, lean_object* v_k_1702_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1698_, v_i_1701_, v_k_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1704_, lean_object* v_keys_1705_, lean_object* v_vals_1706_, lean_object* v_heq_1707_, lean_object* v_i_1708_, lean_object* v_k_1709_){
_start:
{
uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_res_1710_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(v_00_u03b2_1704_, v_keys_1705_, v_vals_1706_, v_heq_1707_, v_i_1708_, v_k_1709_);
lean_dec(v_k_1709_);
lean_dec_ref(v_vals_1706_);
lean_dec_ref(v_keys_1705_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg(lean_object* v_declName_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v_env_1716_; lean_object* v___x_1717_; lean_object* v_ext_1718_; lean_object* v_toEnvExtension_1719_; lean_object* v_asyncMode_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1715_ = lean_st_ref_get(v_a_1713_);
v_env_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc_ref(v_env_1716_);
lean_dec(v___x_1715_);
v___x_1717_ = l_Lean_Meta_Ext_extExtension;
v_ext_1718_ = lean_ctor_get(v___x_1717_, 1);
v_toEnvExtension_1719_ = lean_ctor_get(v_ext_1718_, 0);
v_asyncMode_1720_ = lean_ctor_get(v_toEnvExtension_1719_, 2);
v___x_1721_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1722_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1721_, v___x_1717_, v_env_1716_, v_asyncMode_1720_);
v___x_1723_ = l_Lean_Meta_Ext_ExtTheorems_contains(v___x_1722_, v_declName_1712_);
lean_dec(v___x_1722_);
v___x_1724_ = lean_box(v___x_1723_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg___boxed(lean_object* v_declName_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1726_, v_a_1727_);
lean_dec(v_a_1727_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object* v_declName_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1730_, v_a_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object* v_declName_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Meta_Ext_isExtTheorem(v_declName_1735_, v_a_1736_, v_a_1737_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(lean_object* v_d_1740_, lean_object* v_declName_1741_, lean_object* v_toPure_1742_, lean_object* v_____r_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = l_Lean_Meta_Ext_ExtTheorems_eraseCore(v_d_1740_, v_declName_1741_);
v___x_1745_ = lean_apply_2(v_toPure_1742_, lean_box(0), v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1(lean_object* v___f_1746_, lean_object* v_____r_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_apply_1(v___f_1746_, v_____r_1747_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0));
v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2));
v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg(lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_d_1757_, lean_object* v_declName_1758_){
_start:
{
lean_object* v_toApplicative_1759_; lean_object* v_toBind_1760_; lean_object* v_toPure_1761_; lean_object* v___f_1762_; uint8_t v___x_1763_; 
v_toApplicative_1759_ = lean_ctor_get(v_inst_1755_, 0);
v_toBind_1760_ = lean_ctor_get(v_inst_1755_, 1);
lean_inc(v_toBind_1760_);
v_toPure_1761_ = lean_ctor_get(v_toApplicative_1759_, 1);
lean_inc(v_toPure_1761_);
lean_inc_n(v_declName_1758_, 2);
lean_inc_ref(v_d_1757_);
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1762_, 0, v_d_1757_);
lean_closure_set(v___f_1762_, 1, v_declName_1758_);
lean_closure_set(v___f_1762_, 2, v_toPure_1761_);
v___x_1763_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1757_, v_declName_1758_);
if (v___x_1763_ == 0)
{
lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec_ref(v_d_1757_);
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1764_, 0, v___f_1762_);
v___x_1765_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1);
v___x_1766_ = l_Lean_MessageData_ofConstName(v_declName_1758_, v___x_1763_);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_throwError___redArg(v_inst_1755_, v_inst_1756_, v___x_1769_);
v___x_1771_ = lean_apply_4(v_toBind_1760_, lean_box(0), lean_box(0), v___x_1770_, v___f_1764_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_inc(v_toPure_1761_);
lean_dec_ref(v___f_1762_);
lean_dec(v_toBind_1760_);
lean_dec_ref(v_inst_1756_);
lean_dec_ref(v_inst_1755_);
v___x_1772_ = lean_box(0);
v___x_1773_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(v_d_1757_, v_declName_1758_, v_toPure_1761_, v___x_1772_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object* v_m_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_d_1777_, lean_object* v_declName_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg(v_inst_1775_, v_inst_1776_, v_d_1777_, v_declName_1778_);
return v___x_1779_;
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
