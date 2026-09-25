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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instReprKey_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_extExtension;
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_getExtTheorems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__0 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__0_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__1 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__1_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__2 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__2_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__3 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__3_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__4 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__4_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__5 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__5_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__6 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__6_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__7 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__7_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__8 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__8_value;
static const lean_closure_object l_Lean_Meta_Ext_getExtTheorems___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__9 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Ext_getExtTheorems___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__3_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__4_value)}};
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__10 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Ext_getExtTheorems___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__10_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__5_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__6_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__7_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__8_value)}};
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__11 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Ext_getExtTheorems___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__11_value),((lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__9_value)}};
static const lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__12 = (const lean_object*)&l_Lean_Meta_Ext_getExtTheorems___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
uint64_t v___x_259_; 
v___x_259_ = 1723ULL;
v___y_246_ = v___x_259_;
goto v___jp_245_;
}
else
{
uint64_t v_hash_260_; 
v_hash_260_ = lean_ctor_get_uint64(v_declName_241_, sizeof(void*)*2);
v___y_246_ = v_hash_260_;
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
size_t v___x_255_; size_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; 
v___x_255_ = ((size_t)0ULL);
v___x_256_ = lean_usize_of_nat(v___x_252_);
v___x_257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Ext_instHashableExtTheorem_hash_spec__0(v_keys_243_, v___x_255_, v___x_256_, v___x_250_);
v___x_258_ = lean_uint64_mix_hash(v___x_249_, v___x_257_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instHashableExtTheorem_hash___boxed(lean_object* v_x_261_){
_start:
{
uint64_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Lean_Meta_Ext_instHashableExtTheorem_hash(v_x_261_);
lean_dec_ref(v_x_261_);
v_r_263_ = lean_box_uint64(v_res_262_);
return v_r_263_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_266_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg(){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__1);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___boxed(lean_object* v___dummy_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg();
return v_res_272_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg();
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0(lean_object* v_00_u03b2_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___redArg___closed__0);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Ext_instInhabitedExtTheorems_default_spec__0___closed__0);
v___x_279_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__0);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default(void){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_a_284_);
lean_inc_ref_n(v___x_285_, 2);
v___x_286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_ctor_set(v___x_286_, 2, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_x_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v_x_287_, v_a_288_);
lean_dec_ref(v_x_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10_spec__17(lean_object* v_xs_290_, lean_object* v_v_291_, lean_object* v_i_292_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_array_get_size(v_xs_290_);
v___x_294_ = lean_nat_dec_lt(v_i_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec(v_i_292_);
v___x_295_ = lean_box(0);
return v___x_295_;
}
else
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_array_fget_borrowed(v_xs_290_, v_i_292_);
v___x_297_ = lean_name_eq(v___x_296_, v_v_291_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_add(v_i_292_, v___x_298_);
lean_dec(v_i_292_);
v_i_292_ = v___x_299_;
goto _start;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v_i_292_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10_spec__17___boxed(lean_object* v_xs_302_, lean_object* v_v_303_, lean_object* v_i_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10_spec__17(v_xs_302_, v_v_303_, v_i_304_);
lean_dec(v_v_303_);
lean_dec_ref(v_xs_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10(lean_object* v_xs_306_, lean_object* v_v_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10_spec__17(v_xs_306_, v_v_307_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10___boxed(lean_object* v_xs_310_, lean_object* v_v_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10(v_xs_310_, v_v_311_);
lean_dec(v_v_311_);
lean_dec_ref(v_xs_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(lean_object* v_x_313_, size_t v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v_es_316_; lean_object* v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v_j_320_; lean_object* v_entry_321_; 
v_es_316_ = lean_ctor_get(v_x_313_, 0);
v___x_317_ = lean_box(2);
v___x_318_ = ((size_t)31ULL);
v___x_319_ = lean_usize_land(v_x_314_, v___x_318_);
v_j_320_ = lean_usize_to_nat(v___x_319_);
v_entry_321_ = lean_array_get(v___x_317_, v_es_316_, v_j_320_);
switch(lean_obj_tag(v_entry_321_))
{
case 0:
{
lean_object* v_key_322_; uint8_t v___x_323_; 
v_key_322_ = lean_ctor_get(v_entry_321_, 0);
lean_inc(v_key_322_);
lean_dec_ref_known(v_entry_321_, 2);
v___x_323_ = lean_name_eq(v_x_315_, v_key_322_);
lean_dec(v_key_322_);
if (v___x_323_ == 0)
{
lean_dec(v_j_320_);
return v_x_313_;
}
else
{
lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
lean_inc_ref(v_es_316_);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_x_313_, 0);
lean_dec(v_unused_332_);
v___x_325_ = v_x_313_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_dec(v_x_313_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_array_set(v_es_316_, v_j_320_, v___x_317_);
lean_dec(v_j_320_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
case 1:
{
lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_367_; 
lean_inc_ref(v_es_316_);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v_x_313_, 0);
lean_dec(v_unused_368_);
v___x_334_ = v_x_313_;
v_isShared_335_ = v_isSharedCheck_367_;
goto v_resetjp_333_;
}
else
{
lean_dec(v_x_313_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_367_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_node_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_366_; 
v_node_336_ = lean_ctor_get(v_entry_321_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_entry_321_);
if (v_isSharedCheck_366_ == 0)
{
v___x_338_ = v_entry_321_;
v_isShared_339_ = v_isSharedCheck_366_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_node_336_);
lean_dec(v_entry_321_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_366_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
size_t v___x_340_; lean_object* v_entries_341_; size_t v___x_342_; lean_object* v_newNode_343_; lean_object* v___x_344_; 
v___x_340_ = ((size_t)5ULL);
v_entries_341_ = lean_array_set(v_es_316_, v_j_320_, v___x_317_);
v___x_342_ = lean_usize_shift_right(v_x_314_, v___x_340_);
v_newNode_343_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_node_336_, v___x_342_, v_x_315_);
lean_inc_ref(v_newNode_343_);
v___x_344_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_343_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_346_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v_newNode_343_);
v___x_346_ = v___x_338_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_newNode_343_);
v___x_346_ = v_reuseFailAlloc_351_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = lean_array_set(v_entries_341_, v_j_320_, v___x_346_);
lean_dec(v_j_320_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_347_);
v___x_349_ = v___x_334_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
lean_object* v_val_352_; lean_object* v_fst_353_; lean_object* v_snd_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_newNode_343_);
lean_del_object(v___x_338_);
v_val_352_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v___x_344_, 1);
v_fst_353_ = lean_ctor_get(v_val_352_, 0);
v_snd_354_ = lean_ctor_get(v_val_352_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_val_352_);
if (v_isSharedCheck_365_ == 0)
{
v___x_356_ = v_val_352_;
v_isShared_357_ = v_isSharedCheck_365_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snd_354_);
lean_inc(v_fst_353_);
lean_dec(v_val_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_365_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_fst_353_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_snd_354_);
v___x_359_ = v_reuseFailAlloc_364_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_array_set(v_entries_341_, v_j_320_, v___x_359_);
lean_dec(v_j_320_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_360_);
v___x_362_ = v___x_334_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_320_);
return v_x_313_;
}
}
}
else
{
lean_object* v_ks_369_; lean_object* v_vs_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_384_; 
v_ks_369_ = lean_ctor_get(v_x_313_, 0);
v_vs_370_ = lean_ctor_get(v_x_313_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_384_ == 0)
{
v___x_372_ = v_x_313_;
v_isShared_373_ = v_isSharedCheck_384_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_vs_370_);
lean_inc(v_ks_369_);
lean_dec(v_x_313_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_384_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; 
v___x_374_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4_spec__10(v_ks_369_, v_x_315_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v___x_376_; 
if (v_isShared_373_ == 0)
{
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_ks_369_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_vs_370_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v_val_378_; lean_object* v_keys_x27_379_; lean_object* v_vals_x27_380_; lean_object* v___x_382_; 
v_val_378_ = lean_ctor_get(v___x_374_, 0);
lean_inc_n(v_val_378_, 2);
lean_dec_ref_known(v___x_374_, 1);
v_keys_x27_379_ = l_Array_eraseIdx___redArg(v_ks_369_, v_val_378_);
v_vals_x27_380_ = l_Array_eraseIdx___redArg(v_vs_370_, v_val_378_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v_vals_x27_380_);
lean_ctor_set(v___x_372_, 0, v_keys_x27_379_);
v___x_382_ = v___x_372_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_keys_x27_379_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_vals_x27_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg___boxed(lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
size_t v_x_2797__boxed_388_; lean_object* v_res_389_; 
v_x_2797__boxed_388_ = lean_unbox_usize(v_x_386_);
lean_dec(v_x_386_);
v_res_389_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_385_, v_x_2797__boxed_388_, v_x_387_);
lean_dec(v_x_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
uint64_t v___y_393_; 
if (lean_obj_tag(v_x_391_) == 0)
{
uint64_t v___x_396_; 
v___x_396_ = 1723ULL;
v___y_393_ = v___x_396_;
goto v___jp_392_;
}
else
{
uint64_t v_hash_397_; 
v_hash_397_ = lean_ctor_get_uint64(v_x_391_, sizeof(void*)*2);
v___y_393_ = v_hash_397_;
goto v___jp_392_;
}
v___jp_392_:
{
size_t v_h_394_; lean_object* v___x_395_; 
v_h_394_ = lean_uint64_to_usize(v___y_393_);
v___x_395_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_390_, v_h_394_, v_x_391_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_398_, v_x_399_);
lean_dec(v_x_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13_spec__15___redArg(lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
lean_object* v_ks_405_; lean_object* v_vs_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_430_; 
v_ks_405_ = lean_ctor_get(v_x_401_, 0);
v_vs_406_ = lean_ctor_get(v_x_401_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_x_401_);
if (v_isSharedCheck_430_ == 0)
{
v___x_408_ = v_x_401_;
v_isShared_409_ = v_isSharedCheck_430_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_vs_406_);
lean_inc(v_ks_405_);
lean_dec(v_x_401_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_430_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_ks_405_);
v___x_411_ = lean_nat_dec_lt(v_x_402_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
lean_dec(v_x_402_);
v___x_412_ = lean_array_push(v_ks_405_, v_x_403_);
v___x_413_ = lean_array_push(v_vs_406_, v_x_404_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_413_);
lean_ctor_set(v___x_408_, 0, v___x_412_);
v___x_415_ = v___x_408_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v_k_x27_417_; uint8_t v___x_418_; 
v_k_x27_417_ = lean_array_fget_borrowed(v_ks_405_, v_x_402_);
v___x_418_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_403_, v_k_x27_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_420_; 
if (v_isShared_409_ == 0)
{
v___x_420_ = v___x_408_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_ks_405_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_vs_406_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_x_402_, v___x_421_);
lean_dec(v_x_402_);
v_x_401_ = v___x_420_;
v_x_402_ = v___x_422_;
goto _start;
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_425_ = lean_array_fset(v_ks_405_, v_x_402_, v_x_403_);
v___x_426_ = lean_array_fset(v_vs_406_, v_x_402_, v_x_404_);
lean_dec(v_x_402_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_426_);
lean_ctor_set(v___x_408_, 0, v___x_425_);
v___x_428_ = v___x_408_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13___redArg(lean_object* v_n_431_, lean_object* v_k_432_, lean_object* v_v_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13_spec__15___redArg(v_n_431_, v___x_434_, v_k_432_, v_v_433_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg(lean_object* v_x_437_, size_t v_x_438_, size_t v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_es_442_; size_t v___x_443_; size_t v___x_444_; lean_object* v_j_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_es_442_ = lean_ctor_get(v_x_437_, 0);
v___x_443_ = ((size_t)31ULL);
v___x_444_ = lean_usize_land(v_x_438_, v___x_443_);
v_j_445_ = lean_usize_to_nat(v___x_444_);
v___x_446_ = lean_array_get_size(v_es_442_);
v___x_447_ = lean_nat_dec_lt(v_j_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_dec(v_j_445_);
lean_dec(v_x_441_);
lean_dec(v_x_440_);
return v_x_437_;
}
else
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_486_; 
lean_inc_ref(v_es_442_);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_x_437_, 0);
lean_dec(v_unused_487_);
v___x_449_ = v_x_437_;
v_isShared_450_ = v_isSharedCheck_486_;
goto v_resetjp_448_;
}
else
{
lean_dec(v_x_437_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_486_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_v_451_; lean_object* v___x_452_; lean_object* v_xs_x27_453_; lean_object* v___y_455_; 
v_v_451_ = lean_array_fget(v_es_442_, v_j_445_);
v___x_452_ = lean_box(0);
v_xs_x27_453_ = lean_array_fset(v_es_442_, v_j_445_, v___x_452_);
switch(lean_obj_tag(v_v_451_))
{
case 0:
{
lean_object* v_key_460_; lean_object* v_val_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_471_; 
v_key_460_ = lean_ctor_get(v_v_451_, 0);
v_val_461_ = lean_ctor_get(v_v_451_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_v_451_);
if (v_isSharedCheck_471_ == 0)
{
v___x_463_ = v_v_451_;
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_val_461_);
lean_inc(v_key_460_);
lean_dec(v_v_451_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_471_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_440_, v_key_460_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_del_object(v___x_463_);
v___x_466_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_460_, v_val_461_, v_x_440_, v_x_441_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
v___y_455_ = v___x_467_;
goto v___jp_454_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v_val_461_);
lean_dec(v_key_460_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v_x_441_);
lean_ctor_set(v___x_463_, 0, v_x_440_);
v___x_469_ = v___x_463_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_x_440_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_x_441_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v___y_455_ = v___x_469_;
goto v___jp_454_;
}
}
}
}
case 1:
{
lean_object* v_node_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_484_; 
v_node_472_ = lean_ctor_get(v_v_451_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_v_451_);
if (v_isSharedCheck_484_ == 0)
{
v___x_474_ = v_v_451_;
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_node_472_);
lean_dec(v_v_451_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_484_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_476_ = ((size_t)5ULL);
v___x_477_ = lean_usize_shift_right(v_x_438_, v___x_476_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_add(v_x_439_, v___x_478_);
v___x_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg(v_node_472_, v___x_477_, v___x_479_, v_x_440_, v_x_441_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_480_);
v___x_482_ = v___x_474_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
v___y_455_ = v___x_482_;
goto v___jp_454_;
}
}
}
default: 
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_x_440_);
lean_ctor_set(v___x_485_, 1, v_x_441_);
v___y_455_ = v___x_485_;
goto v___jp_454_;
}
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_array_fset(v_xs_x27_453_, v_j_445_, v___y_455_);
lean_dec(v_j_445_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_456_);
v___x_458_ = v___x_449_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
else
{
lean_object* v_ks_488_; lean_object* v_vs_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_507_; 
v_ks_488_ = lean_ctor_get(v_x_437_, 0);
v_vs_489_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_507_ == 0)
{
v___x_491_ = v_x_437_;
v_isShared_492_ = v_isSharedCheck_507_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_vs_489_);
lean_inc(v_ks_488_);
lean_dec(v_x_437_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_507_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_ks_488_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_vs_489_);
v___x_494_ = v_reuseFailAlloc_506_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v_newNode_495_; size_t v___x_496_; uint8_t v___x_497_; 
v_newNode_495_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13___redArg(v___x_494_, v_x_440_, v_x_441_);
v___x_496_ = ((size_t)7ULL);
v___x_497_ = lean_usize_dec_le(v___x_496_, v_x_439_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_495_);
v___x_499_ = lean_unsigned_to_nat(4u);
v___x_500_ = lean_nat_dec_lt(v___x_498_, v___x_499_);
lean_dec(v___x_498_);
if (v___x_500_ == 0)
{
lean_object* v_ks_501_; lean_object* v_vs_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_ks_501_ = lean_ctor_get(v_newNode_495_, 0);
lean_inc_ref(v_ks_501_);
v_vs_502_ = lean_ctor_get(v_newNode_495_, 1);
lean_inc_ref(v_vs_502_);
lean_dec_ref(v_newNode_495_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0);
v___x_505_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___redArg(v_x_439_, v_ks_501_, v_vs_502_, v___x_503_, v___x_504_);
lean_dec_ref(v_vs_502_);
lean_dec_ref(v_ks_501_);
return v___x_505_;
}
else
{
return v_newNode_495_;
}
}
else
{
return v_newNode_495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___redArg(size_t v_depth_508_, lean_object* v_keys_509_, lean_object* v_vals_510_, lean_object* v_i_511_, lean_object* v_entries_512_){
_start:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_array_get_size(v_keys_509_);
v___x_514_ = lean_nat_dec_lt(v_i_511_, v___x_513_);
if (v___x_514_ == 0)
{
lean_dec(v_i_511_);
return v_entries_512_;
}
else
{
lean_object* v_k_515_; lean_object* v_v_516_; uint64_t v___x_517_; size_t v_h_518_; size_t v___x_519_; lean_object* v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v_h_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_k_515_ = lean_array_fget_borrowed(v_keys_509_, v_i_511_);
v_v_516_ = lean_array_fget_borrowed(v_vals_510_, v_i_511_);
v___x_517_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_515_);
v_h_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = ((size_t)5ULL);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_sub(v_depth_508_, v___x_521_);
v___x_523_ = lean_usize_mul(v___x_519_, v___x_522_);
v_h_524_ = lean_usize_shift_right(v_h_518_, v___x_523_);
v___x_525_ = lean_nat_add(v_i_511_, v___x_520_);
lean_dec(v_i_511_);
lean_inc(v_v_516_);
lean_inc(v_k_515_);
v___x_526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg(v_entries_512_, v_h_524_, v_depth_508_, v_k_515_, v_v_516_);
v_i_511_ = v___x_525_;
v_entries_512_ = v___x_526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_depth_528_, lean_object* v_keys_529_, lean_object* v_vals_530_, lean_object* v_i_531_, lean_object* v_entries_532_){
_start:
{
size_t v_depth_boxed_533_; lean_object* v_res_534_; 
v_depth_boxed_533_ = lean_unbox_usize(v_depth_528_);
lean_dec(v_depth_528_);
v_res_534_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___redArg(v_depth_boxed_533_, v_keys_529_, v_vals_530_, v_i_531_, v_entries_532_);
lean_dec_ref(v_vals_530_);
lean_dec_ref(v_keys_529_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
size_t v_x_3023__boxed_540_; size_t v_x_3024__boxed_541_; lean_object* v_res_542_; 
v_x_3023__boxed_540_ = lean_unbox_usize(v_x_536_);
lean_dec(v_x_536_);
v_x_3024__boxed_541_ = lean_unbox_usize(v_x_537_);
lean_dec(v_x_537_);
v_res_542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg(v_x_535_, v_x_3023__boxed_540_, v_x_3024__boxed_541_, v_x_538_, v_x_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(lean_object* v_xs_543_, lean_object* v_v_544_, lean_object* v_i_545_){
_start:
{
lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_546_ = lean_array_get_size(v_xs_543_);
v___x_547_ = lean_nat_dec_lt(v_i_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec(v_i_545_);
v___x_548_ = lean_box(0);
return v___x_548_;
}
else
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_array_fget_borrowed(v_xs_543_, v_i_545_);
v___x_550_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_549_, v_v_544_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_add(v_i_545_, v___x_551_);
lean_dec(v_i_545_);
v_i_545_ = v___x_552_;
goto _start;
}
else
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_i_545_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_xs_555_, lean_object* v_v_556_, lean_object* v_i_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(v_xs_555_, v_v_556_, v_i_557_);
lean_dec(v_v_556_);
lean_dec_ref(v_xs_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(lean_object* v_xs_559_, lean_object* v_v_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5_spec__11(v_xs_559_, v_v_560_, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5___boxed(lean_object* v_xs_563_, lean_object* v_v_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(v_xs_563_, v_v_564_);
lean_dec(v_v_564_);
lean_dec_ref(v_xs_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_vs_566_, lean_object* v_v_567_, lean_object* v_i_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v_vs_566_);
v___x_570_ = lean_nat_dec_lt(v_i_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v_i_568_);
v___x_571_ = lean_array_push(v_vs_566_, v_v_567_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = lean_array_fget_borrowed(v_vs_566_, v_i_568_);
v___x_573_ = l_Lean_Meta_Ext_instBEqExtTheorem_beq(v_v_567_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_i_568_, v___x_574_);
lean_dec(v_i_568_);
v_i_568_ = v___x_575_;
goto _start;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_array_fset(v_vs_566_, v_i_568_, v_v_567_);
lean_dec(v_i_568_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_vs_578_, lean_object* v_v_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_vs_578_, v_v_579_, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(lean_object* v_a_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_fst_584_; lean_object* v_fst_585_; uint8_t v___x_586_; 
v_fst_584_ = lean_ctor_get(v_a_582_, 0);
v_fst_585_ = lean_ctor_get(v_b_583_, 0);
v___x_586_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_584_, v_fst_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_a_587_, lean_object* v_b_588_){
_start:
{
uint8_t v_res_589_; lean_object* v_r_590_; 
v_res_589_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_a_587_, v_b_588_);
lean_dec_ref(v_b_588_);
lean_dec_ref(v_a_587_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0(lean_object* v_x_591_, lean_object* v_keys_592_, lean_object* v_v_593_, lean_object* v_k_594_, lean_object* v_x_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v_c_598_; lean_object* v___x_599_; 
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_x_591_, v___x_596_);
v_c_598_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_592_, v_v_593_, v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_k_594_);
lean_ctor_set(v___x_599_, 1, v_c_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0___boxed(lean_object* v_x_600_, lean_object* v_keys_601_, lean_object* v_v_602_, lean_object* v_k_603_, lean_object* v_x_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0(v_x_600_, v_keys_601_, v_v_602_, v_k_603_, v_x_604_);
lean_dec_ref(v_keys_601_);
lean_dec(v_x_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___x_606_, lean_object* v_as_607_, lean_object* v_k_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_mid_613_; lean_object* v_midVal_614_; uint8_t v___x_615_; 
v___x_611_ = lean_nat_add(v_x_609_, v_x_610_);
v___x_612_ = lean_unsigned_to_nat(1u);
v_mid_613_ = lean_nat_shiftr(v___x_611_, v___x_612_);
lean_dec(v___x_611_);
v_midVal_614_ = lean_array_fget_borrowed(v_as_607_, v_mid_613_);
v___x_615_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_midVal_614_, v_k_608_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
lean_dec(v_x_610_);
v___x_616_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_k_608_, v_midVal_614_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
lean_dec(v_x_609_);
v___x_617_ = lean_array_get_size(v_as_607_);
v___x_618_ = lean_nat_dec_lt(v_mid_613_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v_mid_613_);
lean_dec_ref(v___x_606_);
return v_as_607_;
}
else
{
lean_object* v___x_619_; lean_object* v_xs_x27_620_; lean_object* v___x_621_; 
v___x_619_ = lean_box(0);
v_xs_x27_620_ = lean_array_fset(v_as_607_, v_mid_613_, v___x_619_);
v___x_621_ = lean_array_fset(v_xs_x27_620_, v_mid_613_, v___x_606_);
lean_dec(v_mid_613_);
return v___x_621_;
}
}
else
{
v_x_610_ = v_mid_613_;
goto _start;
}
}
else
{
uint8_t v___x_623_; 
v___x_623_ = lean_nat_dec_eq(v_mid_613_, v_x_609_);
if (v___x_623_ == 0)
{
lean_dec(v_x_609_);
v_x_609_ = v_mid_613_;
goto _start;
}
else
{
lean_object* v___x_625_; lean_object* v_j_626_; lean_object* v_as_627_; lean_object* v___x_628_; 
lean_dec(v_mid_613_);
lean_dec(v_x_610_);
v___x_625_ = lean_nat_add(v_x_609_, v___x_612_);
lean_dec(v_x_609_);
v_j_626_ = lean_array_get_size(v_as_607_);
v_as_627_ = lean_array_push(v_as_607_, v___x_606_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_625_, v_as_627_, v_j_626_);
lean_dec(v___x_625_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___x_629_, lean_object* v_as_630_, lean_object* v_k_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v___x_629_, v_as_630_, v_k_631_, v_x_632_, v_x_633_);
lean_dec_ref(v_k_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v___x_635_, lean_object* v_as_636_, lean_object* v_k_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_array_get_size(v_as_636_);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_nat_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_array_fget_borrowed(v_as_636_, v___x_639_);
v___x_642_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_k_637_, v___x_641_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
v___x_643_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v___x_641_, v_k_637_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_lt(v___x_639_, v___x_638_);
if (v___x_644_ == 0)
{
lean_dec_ref(v___x_635_);
return v_as_636_;
}
else
{
lean_object* v___x_645_; lean_object* v_xs_x27_646_; lean_object* v___x_647_; 
v___x_645_ = lean_box(0);
v_xs_x27_646_ = lean_array_fset(v_as_636_, v___x_639_, v___x_645_);
v___x_647_ = lean_array_fset(v_xs_x27_646_, v___x_639_, v___x_635_);
return v___x_647_;
}
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_nat_sub(v___x_638_, v___x_648_);
v___x_650_ = lean_array_fget_borrowed(v_as_636_, v___x_649_);
v___x_651_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v___x_650_, v_k_637_);
if (v___x_651_ == 0)
{
uint8_t v___x_652_; 
v___x_652_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_k_637_, v___x_650_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_lt(v___x_649_, v___x_638_);
if (v___x_653_ == 0)
{
lean_dec(v___x_649_);
lean_dec_ref(v___x_635_);
return v_as_636_;
}
else
{
lean_object* v___x_654_; lean_object* v_xs_x27_655_; lean_object* v___x_656_; 
v___x_654_ = lean_box(0);
v_xs_x27_655_ = lean_array_fset(v_as_636_, v___x_649_, v___x_654_);
v___x_656_ = lean_array_fset(v_xs_x27_655_, v___x_649_, v___x_635_);
lean_dec(v___x_649_);
return v___x_656_;
}
}
else
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v___x_635_, v_as_636_, v_k_637_, v___x_639_, v___x_649_);
return v___x_657_;
}
}
else
{
lean_object* v___x_658_; 
lean_dec(v___x_649_);
v___x_658_ = lean_array_push(v_as_636_, v___x_635_);
return v___x_658_;
}
}
}
else
{
lean_object* v_as_659_; lean_object* v___x_660_; 
v_as_659_ = lean_array_push(v_as_636_, v___x_635_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_639_, v_as_659_, v___x_638_);
return v___x_660_;
}
}
else
{
lean_object* v___x_661_; 
v___x_661_ = lean_array_push(v_as_636_, v___x_635_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v___x_662_, lean_object* v_as_663_, lean_object* v_k_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(v___x_662_, v_as_663_, v_k_664_);
lean_dec_ref(v_k_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_x_670_, lean_object* v_keys_671_, lean_object* v_v_672_, lean_object* v_k_673_, lean_object* v_as_674_, lean_object* v_k_675_, lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_mid_680_; lean_object* v_midVal_681_; uint8_t v___x_682_; 
v___x_678_ = lean_nat_add(v_x_676_, v_x_677_);
v___x_679_ = lean_unsigned_to_nat(1u);
v_mid_680_ = lean_nat_shiftr(v___x_678_, v___x_679_);
lean_dec(v___x_678_);
v_midVal_681_ = lean_array_fget(v_as_674_, v_mid_680_);
v___x_682_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_midVal_681_, v_k_675_);
if (v___x_682_ == 0)
{
uint8_t v___x_683_; 
lean_dec(v_x_677_);
v___x_683_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_k_675_, v_midVal_681_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; uint8_t v___x_685_; 
lean_dec(v_x_676_);
v___x_684_ = lean_array_get_size(v_as_674_);
v___x_685_ = lean_nat_dec_lt(v_mid_680_, v___x_684_);
if (v___x_685_ == 0)
{
lean_dec(v_midVal_681_);
lean_dec(v_mid_680_);
lean_dec(v_k_673_);
lean_dec_ref(v_v_672_);
return v_as_674_;
}
else
{
lean_object* v_snd_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_698_; 
v_snd_686_ = lean_ctor_get(v_midVal_681_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_midVal_681_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_midVal_681_, 0);
lean_dec(v_unused_699_);
v___x_688_ = v_midVal_681_;
v_isShared_689_ = v_isSharedCheck_698_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_snd_686_);
lean_dec(v_midVal_681_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_698_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v_xs_x27_691_; lean_object* v___x_692_; lean_object* v_c_693_; lean_object* v___x_695_; 
v___x_690_ = lean_box(0);
v_xs_x27_691_ = lean_array_fset(v_as_674_, v_mid_680_, v___x_690_);
v___x_692_ = lean_nat_add(v_x_670_, v___x_679_);
v_c_693_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_671_, v_v_672_, v___x_692_, v_snd_686_);
lean_dec(v___x_692_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_c_693_);
lean_ctor_set(v___x_688_, 0, v_k_673_);
v___x_695_ = v___x_688_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_k_673_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_c_693_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; 
v___x_696_ = lean_array_fset(v_xs_x27_691_, v_mid_680_, v___x_695_);
lean_dec(v_mid_680_);
return v___x_696_;
}
}
}
}
else
{
lean_dec(v_midVal_681_);
v_x_677_ = v_mid_680_;
goto _start;
}
}
else
{
uint8_t v___x_701_; 
lean_dec(v_midVal_681_);
v___x_701_ = lean_nat_dec_eq(v_mid_680_, v_x_676_);
if (v___x_701_ == 0)
{
lean_dec(v_x_676_);
v_x_676_ = v_mid_680_;
goto _start;
}
else
{
lean_object* v___x_703_; lean_object* v_c_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_j_707_; lean_object* v_as_708_; lean_object* v___x_709_; 
lean_dec(v_mid_680_);
lean_dec(v_x_677_);
v___x_703_ = lean_nat_add(v_x_670_, v___x_679_);
v_c_704_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_671_, v_v_672_, v___x_703_);
lean_dec(v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v_k_673_);
lean_ctor_set(v___x_705_, 1, v_c_704_);
v___x_706_ = lean_nat_add(v_x_676_, v___x_679_);
lean_dec(v_x_676_);
v_j_707_ = lean_array_get_size(v_as_674_);
v_as_708_ = lean_array_push(v_as_674_, v___x_705_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_706_, v_as_708_, v_j_707_);
lean_dec(v___x_706_);
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object* v_x_710_, lean_object* v_keys_711_, lean_object* v_v_712_, lean_object* v_k_713_, lean_object* v_as_714_, lean_object* v_k_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_array_get_size(v_as_714_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_nat_dec_eq(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_array_fget_borrowed(v_as_714_, v___x_717_);
v___x_720_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_k_715_, v___x_719_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v___x_719_, v_k_715_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; 
v___x_722_ = lean_nat_dec_lt(v___x_717_, v___x_716_);
if (v___x_722_ == 0)
{
lean_dec(v_k_713_);
lean_dec_ref(v_v_712_);
return v_as_714_;
}
else
{
lean_object* v___x_723_; lean_object* v_xs_x27_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc(v___x_719_);
v___x_723_ = lean_box(0);
v_xs_x27_724_ = lean_array_fset(v_as_714_, v___x_717_, v___x_723_);
v___x_725_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__2(v_x_710_, v_keys_711_, v_v_712_, v_k_713_, v___x_719_);
v___x_726_ = lean_array_fset(v_xs_x27_724_, v___x_717_, v___x_725_);
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_sub(v___x_716_, v___x_727_);
v___x_729_ = lean_array_fget_borrowed(v_as_714_, v___x_728_);
v___x_730_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v___x_729_, v_k_715_);
if (v___x_730_ == 0)
{
uint8_t v___x_731_; 
v___x_731_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1___lam__0(v_k_715_, v___x_729_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
v___x_732_ = lean_nat_dec_lt(v___x_728_, v___x_716_);
if (v___x_732_ == 0)
{
lean_dec(v___x_728_);
lean_dec(v_k_713_);
lean_dec_ref(v_v_712_);
return v_as_714_;
}
else
{
lean_object* v___x_733_; lean_object* v_xs_x27_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_inc(v___x_729_);
v___x_733_ = lean_box(0);
v_xs_x27_734_ = lean_array_fset(v_as_714_, v___x_728_, v___x_733_);
v___x_735_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__2(v_x_710_, v_keys_711_, v_v_712_, v_k_713_, v___x_729_);
v___x_736_ = lean_array_fset(v_xs_x27_734_, v___x_728_, v___x_735_);
lean_dec(v___x_728_);
return v___x_736_;
}
}
else
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(v_x_710_, v_keys_711_, v_v_712_, v_k_713_, v_as_714_, v_k_715_, v___x_717_, v___x_728_);
return v___x_737_;
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v___x_728_);
v___x_738_ = lean_box(0);
v___x_739_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0(v_x_710_, v_keys_711_, v_v_712_, v_k_713_, v___x_738_);
v___x_740_ = lean_array_push(v_as_714_, v___x_739_);
return v___x_740_;
}
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_as_743_; lean_object* v___x_744_; 
v___x_741_ = lean_box(0);
v___x_742_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0(v_x_710_, v_keys_711_, v_v_712_, v_k_713_, v___x_741_);
v_as_743_ = lean_array_push(v_as_714_, v___x_742_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_717_, v_as_743_, v___x_716_);
return v___x_744_;
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__0(v_x_710_, v_keys_711_, v_v_712_, v_k_713_, v___x_745_);
v___x_747_ = lean_array_push(v_as_714_, v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_keys_748_, lean_object* v_v_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v_key_752_; lean_object* v_child_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_787_; 
v_key_752_ = lean_ctor_get(v_x_751_, 0);
v_child_753_ = lean_ctor_get(v_x_751_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_787_ == 0)
{
v___x_755_ = v_x_751_;
v_isShared_756_ = v_isSharedCheck_787_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_child_753_);
lean_inc(v_key_752_);
lean_dec(v_x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_787_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_array_get_size(v_keys_748_);
v___x_758_ = lean_nat_dec_lt(v_x_750_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_mk_empty_array_with_capacity(v___x_759_);
lean_inc_ref(v___x_760_);
v___x_761_ = lean_array_push(v___x_760_, v_v_749_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_key_752_);
lean_ctor_set(v___x_762_, 1, v_child_753_);
v___x_763_ = lean_array_push(v___x_760_, v___x_762_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 1);
lean_ctor_set(v___x_755_, 1, v___x_763_);
lean_ctor_set(v___x_755_, 0, v___x_761_);
v___x_765_ = v___x_755_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
else
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = lean_array_fget_borrowed(v_keys_748_, v_x_750_);
v___x_768_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_767_, v_key_752_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_key_752_);
lean_ctor_set(v___x_770_, 1, v_child_753_);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_array_push(v___x_772_, v___x_770_);
v___x_774_ = lean_nat_add(v_x_750_, v___x_771_);
v___x_775_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_748_, v_v_749_, v___x_774_);
lean_dec(v___x_774_);
lean_inc(v___x_767_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_767_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
lean_inc_ref(v___x_776_);
v___x_777_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1(v___x_776_, v___x_773_, v___x_776_);
lean_dec_ref_known(v___x_776_, 2);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 1);
lean_ctor_set(v___x_755_, 1, v___x_777_);
lean_ctor_set(v___x_755_, 0, v___x_769_);
v___x_779_ = v___x_755_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_x_750_, v___x_781_);
v___x_783_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_748_, v_v_749_, v___x_782_, v_child_753_);
lean_dec(v___x_782_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_783_);
v___x_785_ = v___x_755_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_key_752_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_object* v_vs_788_; lean_object* v_children_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_806_; 
v_vs_788_ = lean_ctor_get(v_x_751_, 0);
v_children_789_ = lean_ctor_get(v_x_751_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_806_ == 0)
{
v___x_791_ = v_x_751_;
v_isShared_792_ = v_isSharedCheck_806_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_children_789_);
lean_inc(v_vs_788_);
lean_dec(v_x_751_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_806_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_keys_748_);
v___x_794_ = lean_nat_dec_lt(v_x_750_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_vs_788_, v_v_749_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_795_);
v___x_797_ = v___x_791_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_children_789_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
else
{
lean_object* v_k_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v_c_802_; lean_object* v___x_804_; 
v_k_799_ = lean_array_fget_borrowed(v_keys_748_, v_x_750_);
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__1));
lean_inc_n(v_k_799_, 2);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_k_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v_c_802_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_x_750_, v_keys_748_, v_v_749_, v_k_799_, v_children_789_, v___x_801_);
lean_dec_ref_known(v___x_801_, 2);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 1, v_c_802_);
v___x_804_ = v___x_791_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_vs_788_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_c_802_);
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
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__2(lean_object* v_x_807_, lean_object* v_keys_808_, lean_object* v_v_809_, lean_object* v_k_810_, lean_object* v_x_811_){
_start:
{
lean_object* v_snd_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_822_; 
v_snd_812_ = lean_ctor_get(v_x_811_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_811_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_x_811_, 0);
lean_dec(v_unused_823_);
v___x_814_ = v_x_811_;
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_snd_812_);
lean_dec(v_x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_822_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_c_818_; lean_object* v___x_820_; 
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v_x_807_, v___x_816_);
v_c_818_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_808_, v_v_809_, v___x_817_, v_snd_812_);
lean_dec(v___x_817_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_c_818_);
lean_ctor_set(v___x_814_, 0, v_k_810_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_k_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_c_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__2___boxed(lean_object* v_x_824_, lean_object* v_keys_825_, lean_object* v_v_826_, lean_object* v_k_827_, lean_object* v_x_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___lam__2(v_x_824_, v_keys_825_, v_v_826_, v_k_827_, v_x_828_);
lean_dec_ref(v_keys_825_);
lean_dec(v_x_824_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_x_830_, lean_object* v_keys_831_, lean_object* v_v_832_, lean_object* v_k_833_, lean_object* v_as_834_, lean_object* v_k_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(v_x_830_, v_keys_831_, v_v_832_, v_k_833_, v_as_834_, v_k_835_, v_x_836_, v_x_837_);
lean_dec_ref(v_k_835_);
lean_dec_ref(v_keys_831_);
lean_dec(v_x_830_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_keys_839_, lean_object* v_v_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_839_, v_v_840_, v_x_841_, v_x_842_);
lean_dec(v_x_841_);
lean_dec_ref(v_keys_839_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object* v_x_844_, lean_object* v_keys_845_, lean_object* v_v_846_, lean_object* v_k_847_, lean_object* v_as_848_, lean_object* v_k_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_x_844_, v_keys_845_, v_v_846_, v_k_847_, v_as_848_, v_k_849_);
lean_dec_ref(v_k_849_);
lean_dec_ref(v_keys_845_);
lean_dec(v_x_844_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(lean_object* v_keys_851_, lean_object* v_v_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_851_, v_v_852_, v___x_854_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
else
{
lean_object* v_val_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_866_; 
v_val_857_ = lean_ctor_get(v_x_853_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_866_ == 0)
{
v___x_859_ = v_x_853_;
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_val_857_);
lean_dec(v_x_853_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0(v_keys_851_, v_v_852_, v___x_861_, v_val_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_862_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0___boxed(lean_object* v_keys_867_, lean_object* v_v_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_867_, v_v_868_, v_x_869_);
lean_dec_ref(v_keys_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_keys_871_, lean_object* v_v_872_, lean_object* v_x_873_, size_t v_x_874_, size_t v_x_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_object* v_es_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v_j_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_es_877_ = lean_ctor_get(v_x_873_, 0);
v___x_878_ = ((size_t)31ULL);
v___x_879_ = lean_usize_land(v_x_874_, v___x_878_);
v_j_880_ = lean_usize_to_nat(v___x_879_);
v___x_881_ = lean_array_get_size(v_es_877_);
v___x_882_ = lean_nat_dec_lt(v_j_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_dec(v_j_880_);
lean_dec(v_x_876_);
lean_dec_ref(v_v_872_);
return v_x_873_;
}
else
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_950_; 
lean_inc_ref(v_es_877_);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_x_873_, 0);
lean_dec(v_unused_951_);
v___x_884_ = v_x_873_;
v_isShared_885_ = v_isSharedCheck_950_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_x_873_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_950_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_v_886_; lean_object* v___x_887_; lean_object* v_xs_x27_888_; lean_object* v___y_890_; 
v_v_886_ = lean_array_fget(v_es_877_, v_j_880_);
v___x_887_ = lean_box(0);
v_xs_x27_888_ = lean_array_fset(v_es_877_, v_j_880_, v___x_887_);
switch(lean_obj_tag(v_v_886_))
{
case 0:
{
lean_object* v_key_895_; lean_object* v_val_896_; uint8_t v___x_897_; 
v_key_895_ = lean_ctor_get(v_v_886_, 0);
v_val_896_ = lean_ctor_get(v_v_886_, 1);
v___x_897_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_876_, v_key_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_box(0);
v___x_899_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_871_, v_v_872_, v___x_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_dec(v_x_876_);
v___y_890_ = v_v_886_;
goto v___jp_889_;
}
else
{
lean_object* v_val_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_908_; 
lean_inc(v_val_896_);
lean_inc(v_key_895_);
lean_dec_ref_known(v_v_886_, 2);
v_val_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_908_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_val_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_895_, v_val_896_, v_x_876_, v_val_900_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v___y_890_ = v___x_906_;
goto v___jp_889_;
}
}
}
}
else
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_919_; 
lean_inc(v_val_896_);
v_isSharedCheck_919_ = !lean_is_exclusive(v_v_886_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; lean_object* v_unused_921_; 
v_unused_920_ = lean_ctor_get(v_v_886_, 1);
lean_dec(v_unused_920_);
v_unused_921_ = lean_ctor_get(v_v_886_, 0);
lean_dec(v_unused_921_);
v___x_910_ = v_v_886_;
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
else
{
lean_dec(v_v_886_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_val_896_);
v___x_913_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_871_, v_v_872_, v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; 
lean_del_object(v___x_910_);
lean_dec(v_x_876_);
v___x_914_ = lean_box(2);
v___y_890_ = v___x_914_;
goto v___jp_889_;
}
else
{
lean_object* v_val_915_; lean_object* v___x_917_; 
v_val_915_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v___x_913_, 1);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v_val_915_);
lean_ctor_set(v___x_910_, 0, v_x_876_);
v___x_917_ = v___x_910_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_x_876_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_val_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
v___y_890_ = v___x_917_;
goto v___jp_889_;
}
}
}
}
}
case 1:
{
lean_object* v_node_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_945_; 
v_node_922_ = lean_ctor_get(v_v_886_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_v_886_);
if (v_isSharedCheck_945_ == 0)
{
v___x_924_ = v_v_886_;
v_isShared_925_ = v_isSharedCheck_945_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_node_922_);
lean_dec(v_v_886_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_945_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; size_t v___x_929_; lean_object* v_newNode_930_; lean_object* v___x_931_; 
v___x_926_ = ((size_t)5ULL);
v___x_927_ = lean_usize_shift_right(v_x_874_, v___x_926_);
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_x_875_, v___x_928_);
v_newNode_930_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_871_, v_v_872_, v_node_922_, v___x_927_, v___x_929_, v_x_876_);
lean_inc_ref(v_newNode_930_);
v___x_931_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_930_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_933_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_newNode_930_);
v___x_933_ = v___x_924_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_newNode_930_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
v___y_890_ = v___x_933_;
goto v___jp_889_;
}
}
else
{
lean_object* v_val_935_; lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_newNode_930_);
lean_del_object(v___x_924_);
v_val_935_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v___x_931_, 1);
v_fst_936_ = lean_ctor_get(v_val_935_, 0);
v_snd_937_ = lean_ctor_get(v_val_935_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_val_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v_val_935_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snd_937_);
lean_inc(v_fst_936_);
lean_dec(v_val_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_fst_936_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_snd_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
v___y_890_ = v___x_942_;
goto v___jp_889_;
}
}
}
}
}
default: 
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_box(0);
v___x_947_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_871_, v_v_872_, v___x_946_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_dec(v_x_876_);
v___y_890_ = v_v_886_;
goto v___jp_889_;
}
else
{
lean_object* v_val_948_; lean_object* v___x_949_; 
v_val_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v___x_947_, 1);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_x_876_);
lean_ctor_set(v___x_949_, 1, v_val_948_);
v___y_890_ = v___x_949_;
goto v___jp_889_;
}
}
}
v___jp_889_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_array_fset(v_xs_x27_888_, v_j_880_, v___y_890_);
lean_dec(v_j_880_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_891_);
v___x_893_ = v___x_884_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
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
else
{
lean_object* v_ks_952_; lean_object* v_vs_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_986_; 
v_ks_952_ = lean_ctor_get(v_x_873_, 0);
v_vs_953_ = lean_ctor_get(v_x_873_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_986_ == 0)
{
v___x_955_ = v_x_873_;
v_isShared_956_ = v_isSharedCheck_986_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_vs_953_);
lean_inc(v_ks_952_);
lean_dec(v_x_873_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_986_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; 
v___x_957_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__5(v_ks_952_, v_x_876_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_959_; 
if (v_isShared_956_ == 0)
{
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_ks_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_vs_953_);
v___x_959_ = v_reuseFailAlloc_964_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_box(0);
v___x_961_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_871_, v_v_872_, v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_dec(v_x_876_);
return v___x_959_;
}
else
{
lean_object* v_val_962_; lean_object* v___x_963_; 
v_val_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_val_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg(v___x_959_, v_x_874_, v_x_875_, v_x_876_, v_val_962_);
return v___x_963_;
}
}
}
else
{
lean_object* v_val_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_985_; 
v_val_965_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_985_ == 0)
{
v___x_967_ = v___x_957_;
v_isShared_968_ = v_isSharedCheck_985_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_val_965_);
lean_dec(v___x_957_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_985_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_v_x27_969_; lean_object* v_keys_970_; lean_object* v_vals_971_; lean_object* v___x_973_; 
v_v_x27_969_ = lean_array_fget(v_vs_953_, v_val_965_);
lean_inc(v_val_965_);
v_keys_970_ = l_Array_eraseIdx___redArg(v_ks_952_, v_val_965_);
v_vals_971_ = l_Array_eraseIdx___redArg(v_vs_953_, v_val_965_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_v_x27_969_);
v___x_973_ = v___x_967_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_v_x27_969_);
v___x_973_ = v_reuseFailAlloc_984_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___lam__0(v_keys_871_, v_v_872_, v___x_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_976_; 
lean_dec(v_x_876_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_vals_971_);
lean_ctor_set(v___x_955_, 0, v_keys_970_);
v___x_976_ = v___x_955_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_keys_970_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_vals_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_object* v_val_978_; lean_object* v_keys_979_; lean_object* v_vals_980_; lean_object* v___x_982_; 
v_val_978_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_978_);
lean_dec_ref_known(v___x_974_, 1);
v_keys_979_ = lean_array_push(v_keys_970_, v_x_876_);
v_vals_980_ = lean_array_push(v_vals_971_, v_val_978_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_vals_980_);
lean_ctor_set(v___x_955_, 0, v_keys_979_);
v___x_982_ = v___x_955_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_keys_979_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_vals_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_keys_987_, lean_object* v_v_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
size_t v_x_3620__boxed_993_; size_t v_x_3621__boxed_994_; lean_object* v_res_995_; 
v_x_3620__boxed_993_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_x_3621__boxed_994_ = lean_unbox_usize(v_x_991_);
lean_dec(v_x_991_);
v_res_995_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_987_, v_v_988_, v_x_989_, v_x_3620__boxed_993_, v_x_3621__boxed_994_, v_x_992_);
lean_dec_ref(v_keys_987_);
return v_res_995_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_DiscrTree_instInhabited___redArg();
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_msg_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2___closed__0);
v___x_999_ = lean_panic_fn_borrowed(v___x_998_, v_msg_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1003_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__2));
v___x_1004_ = lean_unsigned_to_nat(23u);
v___x_1005_ = lean_unsigned_to_nat(177u);
v___x_1006_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__1));
v___x_1007_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__0));
v___x_1008_ = l_mkPanicMessageWithDecl(v___x_1007_, v___x_1006_, v___x_1005_, v___x_1004_, v___x_1003_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(lean_object* v_d_1009_, lean_object* v_keys_1010_, lean_object* v_v_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1012_ = lean_array_get_size(v_keys_1010_);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_nat_dec_eq(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v_k_1016_; uint64_t v___x_1017_; size_t v_h_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1015_ = lean_box(0);
v_k_1016_ = lean_array_get_borrowed(v___x_1015_, v_keys_1010_, v___x_1013_);
v___x_1017_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1016_);
v_h_1018_ = lean_uint64_to_usize(v___x_1017_);
v___x_1019_ = ((size_t)1ULL);
lean_inc(v_k_1016_);
v___x_1020_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1(v_keys_1010_, v_v_1011_, v_d_1009_, v_h_1018_, v___x_1019_, v_k_1016_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v_v_1011_);
lean_dec_ref(v_d_1009_);
v___x_1021_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___closed__3);
v___x_1022_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__2(v___x_1021_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_1023_, lean_object* v_keys_1024_, lean_object* v_v_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_d_1023_, v_keys_1024_, v_v_1025_);
lean_dec_ref(v_keys_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v_x_1027_, lean_object* v_thm_1028_){
_start:
{
lean_object* v_tree_1029_; lean_object* v_erased_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1041_; 
v_tree_1029_ = lean_ctor_get(v_x_1027_, 0);
v_erased_1030_ = lean_ctor_get(v_x_1027_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_x_1027_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1032_ = v_x_1027_;
v_isShared_1033_ = v_isSharedCheck_1041_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_erased_1030_);
lean_inc(v_tree_1029_);
lean_dec(v_x_1027_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1041_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_declName_1034_; lean_object* v_keys_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v_declName_1034_ = lean_ctor_get(v_thm_1028_, 0);
lean_inc(v_declName_1034_);
v_keys_1035_ = lean_ctor_get(v_thm_1028_, 2);
lean_inc_ref(v_keys_1035_);
v___x_1036_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0(v_tree_1029_, v_keys_1035_, v_thm_1028_);
lean_dec_ref(v_keys_1035_);
v___x_1037_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_erased_1030_, v_declName_1034_);
lean_dec(v_declName_1034_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___x_1037_);
lean_ctor_set(v___x_1032_, 0, v___x_1036_);
v___x_1039_ = v___x_1032_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(lean_object* v___y_1042_){
_start:
{
lean_inc_ref(v___y_1042_);
return v___y_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___lam__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(v___y_1043_);
lean_dec_ref(v___y_1043_);
return v_res_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___f_1057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__0_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___f_1058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__2_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_1059_ = lean_obj_once(&l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1, &l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1_once, _init_l_Lean_Meta_Ext_instInhabitedExtTheorems_default___closed__1);
v___f_1060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__1_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__7_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_));
v___x_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___f_1060_);
lean_ctor_set(v___x_1062_, 2, v___x_1059_);
lean_ctor_set(v___x_1062_, 3, v___f_1058_);
lean_ctor_set(v___x_1062_, 4, v___f_1057_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn___closed__8_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_);
v___x_1065_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2____boxed(lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2_();
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1068_, lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___redArg(v_x_1069_, v_x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1(v_00_u03b2_1072_, v_x_1073_, v_x_1074_);
lean_dec(v_x_1074_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, size_t v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___redArg(v_x_1077_, v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4___boxed(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
size_t v_x_3989__boxed_1085_; lean_object* v_res_1086_; 
v_x_3989__boxed_1085_ = lean_unbox_usize(v_x_1083_);
lean_dec(v_x_1083_);
v_res_1086_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__1_spec__4(v_00_u03b2_1081_, v_x_1082_, v_x_3989__boxed_1085_, v_x_1084_);
lean_dec(v_x_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, size_t v_x_1089_, size_t v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg(v_x_1088_, v_x_1089_, v_x_1090_, v_x_1091_, v_x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
size_t v_x_4000__boxed_1100_; size_t v_x_4001__boxed_1101_; lean_object* v_res_1102_; 
v_x_4000__boxed_1100_ = lean_unbox_usize(v_x_1096_);
lean_dec(v_x_1096_);
v_x_4001__boxed_1101_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_res_1102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6(v_00_u03b2_1094_, v_x_1095_, v_x_4000__boxed_1100_, v_x_4001__boxed_1101_, v_x_1098_, v_x_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v___x_1103_, lean_object* v_as_1104_, lean_object* v_k_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v___x_1103_, v_as_1104_, v_k_1105_, v_x_1106_, v_x_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1111_, lean_object* v_as_1112_, lean_object* v_k_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v___x_1111_, v_as_1112_, v_k_1113_, v_x_1114_, v_x_1115_, v_x_1116_, v_x_1117_);
lean_dec_ref(v_k_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8(lean_object* v_x_1119_, lean_object* v_keys_1120_, lean_object* v_v_1121_, lean_object* v_k_1122_, lean_object* v_as_1123_, lean_object* v_k_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___redArg(v_x_1119_, v_keys_1120_, v_v_1121_, v_k_1122_, v_as_1123_, v_k_1124_, v_x_1125_, v_x_1126_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_x_1130_, lean_object* v_keys_1131_, lean_object* v_v_1132_, lean_object* v_k_1133_, lean_object* v_as_1134_, lean_object* v_k_1135_, lean_object* v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0_spec__3_spec__8(v_x_1130_, v_keys_1131_, v_v_1132_, v_k_1133_, v_as_1134_, v_k_1135_, v_x_1136_, v_x_1137_, v_x_1138_, v_x_1139_);
lean_dec_ref(v_k_1135_);
lean_dec_ref(v_keys_1131_);
lean_dec(v_x_1130_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13(lean_object* v_00_u03b2_1141_, lean_object* v_n_1142_, lean_object* v_k_1143_, lean_object* v_v_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13___redArg(v_n_1142_, v_k_1143_, v_v_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_1146_, size_t v_depth_1147_, lean_object* v_keys_1148_, lean_object* v_vals_1149_, lean_object* v_heq_1150_, lean_object* v_i_1151_, lean_object* v_entries_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___redArg(v_depth_1147_, v_keys_1148_, v_vals_1149_, v_i_1151_, v_entries_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_1154_, lean_object* v_depth_1155_, lean_object* v_keys_1156_, lean_object* v_vals_1157_, lean_object* v_heq_1158_, lean_object* v_i_1159_, lean_object* v_entries_1160_){
_start:
{
size_t v_depth_boxed_1161_; lean_object* v_res_1162_; 
v_depth_boxed_1161_ = lean_unbox_usize(v_depth_1155_);
lean_dec(v_depth_1155_);
v_res_1162_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__14(v_00_u03b2_1154_, v_depth_boxed_1161_, v_keys_1156_, v_vals_1157_, v_heq_1158_, v_i_1159_, v_entries_1160_);
lean_dec_ref(v_vals_1157_);
lean_dec_ref(v_keys_1156_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6_spec__13_spec__15___redArg(v_x_1164_, v_x_1165_, v_x_1166_, v_x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_getExtTheorems___lam__0(lean_object* v_x1_1169_, lean_object* v_x2_1170_){
_start:
{
lean_object* v_priority_1171_; lean_object* v_priority_1172_; uint8_t v___x_1173_; 
v_priority_1171_ = lean_ctor_get(v_x1_1169_, 1);
v_priority_1172_ = lean_ctor_get(v_x2_1170_, 1);
v___x_1173_ = lean_nat_dec_lt(v_priority_1171_, v_priority_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__0___boxed(lean_object* v_x1_1174_, lean_object* v_x2_1175_){
_start:
{
uint8_t v_res_1176_; lean_object* v_r_1177_; 
v_res_1176_ = l_Lean_Meta_Ext_getExtTheorems___lam__0(v_x1_1174_, v_x2_1175_);
lean_dec_ref(v_x2_1175_);
lean_dec_ref(v_x1_1174_);
v_r_1177_ = lean_box(v_res_1176_);
return v_r_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___lam__1(lean_object* v___x_1178_, lean_object* v___x_1179_, lean_object* v___x_1180_, lean_object* v_x1_1181_, lean_object* v_x2_1182_){
_start:
{
lean_object* v_erased_1183_; lean_object* v_declName_1184_; uint8_t v___x_1185_; 
v_erased_1183_ = lean_ctor_get(v___x_1178_, 1);
lean_inc_ref(v_erased_1183_);
lean_dec(v___x_1178_);
v_declName_1184_ = lean_ctor_get(v_x2_1182_, 0);
lean_inc(v_declName_1184_);
v___x_1185_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1179_, v___x_1180_, v_erased_1183_, v_declName_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_array_push(v_x1_1181_, v_x2_1182_);
return v___x_1186_;
}
else
{
lean_dec_ref(v_x2_1182_);
return v_x1_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object* v_ty_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_env_1220_; lean_object* v___x_1221_; lean_object* v_ext_1222_; lean_object* v_toEnvExtension_1223_; lean_object* v_asyncMode_1224_; lean_object* v___x_1225_; lean_object* v_tree_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
v___f_1215_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__0));
v___x_1216_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1217_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__1));
v___x_1218_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__2));
v___x_1219_ = lean_st_ref_get(v_a_1213_);
v_env_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc_ref(v_env_1220_);
lean_dec(v___x_1219_);
v___x_1221_ = l_Lean_Meta_Ext_extExtension;
v_ext_1222_ = lean_ctor_get(v___x_1221_, 1);
v_toEnvExtension_1223_ = lean_ctor_get(v_ext_1222_, 0);
v_asyncMode_1224_ = lean_ctor_get(v_toEnvExtension_1223_, 2);
v___x_1225_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1216_, v___x_1221_, v_env_1220_, v_asyncMode_1224_);
v_tree_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_ref(v_tree_1226_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_getExtTheorems___lam__1), 5, 3);
lean_closure_set(v___f_1227_, 0, v___x_1225_);
lean_closure_set(v___f_1227_, 1, v___x_1217_);
lean_closure_set(v___f_1227_, 2, v___x_1218_);
v___x_1228_ = l_Lean_Meta_DiscrTree_getMatch___redArg(v_tree_1226_, v_ty_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec_ref(v_tree_1226_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1254_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1254_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1254_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___y_1234_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_array_get_size(v_a_1229_);
v___x_1244_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_1245_ = ((lean_object*)(l_Lean_Meta_Ext_getExtTheorems___closed__12));
v___x_1246_ = lean_nat_dec_lt(v___x_1242_, v___x_1243_);
if (v___x_1246_ == 0)
{
lean_dec(v_a_1229_);
lean_dec_ref(v___f_1227_);
v___y_1234_ = v___x_1244_;
goto v___jp_1233_;
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_nat_dec_le(v___x_1243_, v___x_1243_);
if (v___x_1247_ == 0)
{
if (v___x_1246_ == 0)
{
lean_dec(v_a_1229_);
lean_dec_ref(v___f_1227_);
v___y_1234_ = v___x_1244_;
goto v___jp_1233_;
}
else
{
size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = lean_usize_of_nat(v___x_1243_);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1245_, v___f_1227_, v_a_1229_, v___x_1248_, v___x_1249_, v___x_1244_);
v___y_1234_ = v___x_1250_;
goto v___jp_1233_;
}
}
else
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = ((size_t)0ULL);
v___x_1252_ = lean_usize_of_nat(v___x_1243_);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1245_, v___f_1227_, v_a_1229_, v___x_1251_, v___x_1252_, v___x_1244_);
v___y_1234_ = v___x_1253_;
goto v___jp_1233_;
}
}
v___jp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_array_get_size(v___y_1234_);
v___x_1237_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse(lean_box(0), v___f_1215_, v___y_1234_, v___x_1235_, v___x_1236_);
v___x_1238_ = l_Array_reverse___redArg(v___x_1237_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1238_);
v___x_1240_ = v___x_1231_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_dec_ref(v___f_1227_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems___boxed(lean_object* v_ty_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_Ext_getExtTheorems(v_ty_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v_ks_1266_; lean_object* v_vs_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1291_; 
v_ks_1266_ = lean_ctor_get(v_x_1262_, 0);
v_vs_1267_ = lean_ctor_get(v_x_1262_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_x_1262_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1269_ = v_x_1262_;
v_isShared_1270_ = v_isSharedCheck_1291_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_vs_1267_);
lean_inc(v_ks_1266_);
lean_dec(v_x_1262_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1291_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = lean_array_get_size(v_ks_1266_);
v___x_1272_ = lean_nat_dec_lt(v_x_1263_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
lean_dec(v_x_1263_);
v___x_1273_ = lean_array_push(v_ks_1266_, v_x_1264_);
v___x_1274_ = lean_array_push(v_vs_1267_, v_x_1265_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v___x_1274_);
lean_ctor_set(v___x_1269_, 0, v___x_1273_);
v___x_1276_ = v___x_1269_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
else
{
lean_object* v_k_x27_1278_; uint8_t v___x_1279_; 
v_k_x27_1278_ = lean_array_fget_borrowed(v_ks_1266_, v_x_1263_);
v___x_1279_ = lean_name_eq(v_x_1264_, v_k_x27_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1281_; 
if (v_isShared_1270_ == 0)
{
v___x_1281_ = v___x_1269_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_ks_1266_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_vs_1267_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_nat_add(v_x_1263_, v___x_1282_);
lean_dec(v_x_1263_);
v_x_1262_ = v___x_1281_;
v_x_1263_ = v___x_1283_;
goto _start;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1286_ = lean_array_fset(v_ks_1266_, v_x_1263_, v_x_1264_);
v___x_1287_ = lean_array_fset(v_vs_1267_, v_x_1263_, v_x_1265_);
lean_dec(v_x_1263_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v___x_1287_);
lean_ctor_set(v___x_1269_, 0, v___x_1286_);
v___x_1289_ = v___x_1269_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1292_, lean_object* v_k_1293_, lean_object* v_v_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(0u);
v___x_1296_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1292_, v___x_1295_, v_k_1293_, v_v_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(lean_object* v_x_1297_, size_t v_x_1298_, size_t v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_){
_start:
{
if (lean_obj_tag(v_x_1297_) == 0)
{
lean_object* v_es_1302_; size_t v___x_1303_; size_t v___x_1304_; lean_object* v_j_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_es_1302_ = lean_ctor_get(v_x_1297_, 0);
v___x_1303_ = ((size_t)31ULL);
v___x_1304_ = lean_usize_land(v_x_1298_, v___x_1303_);
v_j_1305_ = lean_usize_to_nat(v___x_1304_);
v___x_1306_ = lean_array_get_size(v_es_1302_);
v___x_1307_ = lean_nat_dec_lt(v_j_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v_j_1305_);
lean_dec(v_x_1301_);
lean_dec(v_x_1300_);
return v_x_1297_;
}
else
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1346_; 
lean_inc_ref(v_es_1302_);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_x_1297_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_x_1297_, 0);
lean_dec(v_unused_1347_);
v___x_1309_ = v_x_1297_;
v_isShared_1310_ = v_isSharedCheck_1346_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v_x_1297_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1346_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_v_1311_; lean_object* v___x_1312_; lean_object* v_xs_x27_1313_; lean_object* v___y_1315_; 
v_v_1311_ = lean_array_fget(v_es_1302_, v_j_1305_);
v___x_1312_ = lean_box(0);
v_xs_x27_1313_ = lean_array_fset(v_es_1302_, v_j_1305_, v___x_1312_);
switch(lean_obj_tag(v_v_1311_))
{
case 0:
{
lean_object* v_key_1320_; lean_object* v_val_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1331_; 
v_key_1320_ = lean_ctor_get(v_v_1311_, 0);
v_val_1321_ = lean_ctor_get(v_v_1311_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_v_1311_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1323_ = v_v_1311_;
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_val_1321_);
lean_inc(v_key_1320_);
lean_dec(v_v_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_name_eq(v_x_1300_, v_key_1320_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_del_object(v___x_1323_);
v___x_1326_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1320_, v_val_1321_, v_x_1300_, v_x_1301_);
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
v___y_1315_ = v___x_1327_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1329_; 
lean_dec(v_val_1321_);
lean_dec(v_key_1320_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v_x_1301_);
lean_ctor_set(v___x_1323_, 0, v_x_1300_);
v___x_1329_ = v___x_1323_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_x_1300_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_x_1301_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v___y_1315_ = v___x_1329_;
goto v___jp_1314_;
}
}
}
}
case 1:
{
lean_object* v_node_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1344_; 
v_node_1332_ = lean_ctor_get(v_v_1311_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_v_1311_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1334_ = v_v_1311_;
v_isShared_1335_ = v_isSharedCheck_1344_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_node_1332_);
lean_dec(v_v_1311_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1344_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
size_t v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1336_ = ((size_t)5ULL);
v___x_1337_ = lean_usize_shift_right(v_x_1298_, v___x_1336_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_x_1299_, v___x_1338_);
v___x_1340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_node_1332_, v___x_1337_, v___x_1339_, v_x_1300_, v_x_1301_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1340_);
v___x_1342_ = v___x_1334_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
v___y_1315_ = v___x_1342_;
goto v___jp_1314_;
}
}
}
default: 
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_x_1300_);
lean_ctor_set(v___x_1345_, 1, v_x_1301_);
v___y_1315_ = v___x_1345_;
goto v___jp_1314_;
}
}
v___jp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_array_fset(v_xs_x27_1313_, v_j_1305_, v___y_1315_);
lean_dec(v_j_1305_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1316_);
v___x_1318_ = v___x_1309_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
else
{
lean_object* v_ks_1348_; lean_object* v_vs_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1367_; 
v_ks_1348_ = lean_ctor_get(v_x_1297_, 0);
v_vs_1349_ = lean_ctor_get(v_x_1297_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1297_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1351_ = v_x_1297_;
v_isShared_1352_ = v_isSharedCheck_1367_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_vs_1349_);
lean_inc(v_ks_1348_);
lean_dec(v_x_1297_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1367_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_ks_1348_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_vs_1349_);
v___x_1354_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v_newNode_1355_; size_t v___x_1356_; uint8_t v___x_1357_; 
v_newNode_1355_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v___x_1354_, v_x_1300_, v_x_1301_);
v___x_1356_ = ((size_t)7ULL);
v___x_1357_ = lean_usize_dec_le(v___x_1356_, v_x_1299_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1358_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1355_);
v___x_1359_ = lean_unsigned_to_nat(4u);
v___x_1360_ = lean_nat_dec_lt(v___x_1358_, v___x_1359_);
lean_dec(v___x_1358_);
if (v___x_1360_ == 0)
{
lean_object* v_ks_1361_; lean_object* v_vs_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_ks_1361_ = lean_ctor_get(v_newNode_1355_, 0);
lean_inc_ref(v_ks_1361_);
v_vs_1362_ = lean_ctor_get(v_newNode_1355_, 1);
lean_inc_ref(v_vs_1362_);
lean_dec_ref(v_newNode_1355_);
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00__private_Lean_Meta_Tactic_Ext_0__Lean_Meta_Ext_initFn_00___x40_Lean_Meta_Tactic_Ext_3056382534____hygCtx___hyg_2__spec__0_spec__1_spec__6___redArg___closed__0);
v___x_1365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_x_1299_, v_ks_1361_, v_vs_1362_, v___x_1363_, v___x_1364_);
lean_dec_ref(v_vs_1362_);
lean_dec_ref(v_ks_1361_);
return v___x_1365_;
}
else
{
return v_newNode_1355_;
}
}
else
{
return v_newNode_1355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(size_t v_depth_1368_, lean_object* v_keys_1369_, lean_object* v_vals_1370_, lean_object* v_i_1371_, lean_object* v_entries_1372_){
_start:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_array_get_size(v_keys_1369_);
v___x_1374_ = lean_nat_dec_lt(v_i_1371_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_dec(v_i_1371_);
return v_entries_1372_;
}
else
{
lean_object* v_k_1375_; lean_object* v_v_1376_; uint64_t v___y_1378_; 
v_k_1375_ = lean_array_fget_borrowed(v_keys_1369_, v_i_1371_);
v_v_1376_ = lean_array_fget_borrowed(v_vals_1370_, v_i_1371_);
if (lean_obj_tag(v_k_1375_) == 0)
{
uint64_t v___x_1389_; 
v___x_1389_ = 1723ULL;
v___y_1378_ = v___x_1389_;
goto v___jp_1377_;
}
else
{
uint64_t v_hash_1390_; 
v_hash_1390_ = lean_ctor_get_uint64(v_k_1375_, sizeof(void*)*2);
v___y_1378_ = v_hash_1390_;
goto v___jp_1377_;
}
v___jp_1377_:
{
size_t v_h_1379_; size_t v___x_1380_; lean_object* v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; size_t v_h_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_h_1379_ = lean_uint64_to_usize(v___y_1378_);
v___x_1380_ = ((size_t)5ULL);
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_sub(v_depth_1368_, v___x_1382_);
v___x_1384_ = lean_usize_mul(v___x_1380_, v___x_1383_);
v_h_1385_ = lean_usize_shift_right(v_h_1379_, v___x_1384_);
v___x_1386_ = lean_nat_add(v_i_1371_, v___x_1381_);
lean_dec(v_i_1371_);
lean_inc(v_v_1376_);
lean_inc(v_k_1375_);
v___x_1387_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_entries_1372_, v_h_1385_, v_depth_1368_, v_k_1375_, v_v_1376_);
v_i_1371_ = v___x_1386_;
v_entries_1372_ = v___x_1387_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1391_, lean_object* v_keys_1392_, lean_object* v_vals_1393_, lean_object* v_i_1394_, lean_object* v_entries_1395_){
_start:
{
size_t v_depth_boxed_1396_; lean_object* v_res_1397_; 
v_depth_boxed_1396_ = lean_unbox_usize(v_depth_1391_);
lean_dec(v_depth_1391_);
v_res_1397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1396_, v_keys_1392_, v_vals_1393_, v_i_1394_, v_entries_1395_);
lean_dec_ref(v_vals_1393_);
lean_dec_ref(v_keys_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v_x_1402_){
_start:
{
size_t v_x_364__boxed_1403_; size_t v_x_365__boxed_1404_; lean_object* v_res_1405_; 
v_x_364__boxed_1403_ = lean_unbox_usize(v_x_1399_);
lean_dec(v_x_1399_);
v_x_365__boxed_1404_ = lean_unbox_usize(v_x_1400_);
lean_dec(v_x_1400_);
v_res_1405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1398_, v_x_364__boxed_1403_, v_x_365__boxed_1404_, v_x_1401_, v_x_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
uint64_t v___y_1410_; 
if (lean_obj_tag(v_x_1407_) == 0)
{
uint64_t v___x_1414_; 
v___x_1414_ = 1723ULL;
v___y_1410_ = v___x_1414_;
goto v___jp_1409_;
}
else
{
uint64_t v_hash_1415_; 
v_hash_1415_ = lean_ctor_get_uint64(v_x_1407_, sizeof(void*)*2);
v___y_1410_ = v_hash_1415_;
goto v___jp_1409_;
}
v___jp_1409_:
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = lean_uint64_to_usize(v___y_1410_);
v___x_1412_ = ((size_t)1ULL);
v___x_1413_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1406_, v___x_1411_, v___x_1412_, v_x_1407_, v_x_1408_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object* v_d_1416_, lean_object* v_declName_1417_){
_start:
{
lean_object* v_tree_1418_; lean_object* v_erased_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1428_; 
v_tree_1418_ = lean_ctor_get(v_d_1416_, 0);
v_erased_1419_ = lean_ctor_get(v_d_1416_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_d_1416_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1421_ = v_d_1416_;
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_erased_1419_);
lean_inc(v_tree_1418_);
lean_dec(v_d_1416_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1428_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_erased_1419_, v_declName_1417_, v___x_1423_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v___x_1424_);
v___x_1426_ = v___x_1421_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_tree_1418_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0(lean_object* v_00_u03b2_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0___redArg(v_x_1430_, v_x_1431_, v_x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, size_t v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___redArg(v_x_1435_, v_x_1436_, v_x_1437_, v_x_1438_, v_x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
size_t v_x_561__boxed_1447_; size_t v_x_562__boxed_1448_; lean_object* v_res_1449_; 
v_x_561__boxed_1447_ = lean_unbox_usize(v_x_1443_);
lean_dec(v_x_1443_);
v_x_562__boxed_1448_ = lean_unbox_usize(v_x_1444_);
lean_dec(v_x_1444_);
v_res_1449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0(v_00_u03b2_1441_, v_x_1442_, v_x_561__boxed_1447_, v_x_562__boxed_1448_, v_x_1445_, v_x_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1450_, lean_object* v_n_1451_, lean_object* v_k_1452_, lean_object* v_v_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1___redArg(v_n_1451_, v_k_1452_, v_v_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1455_, size_t v_depth_1456_, lean_object* v_keys_1457_, lean_object* v_vals_1458_, lean_object* v_heq_1459_, lean_object* v_i_1460_, lean_object* v_entries_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___redArg(v_depth_1456_, v_keys_1457_, v_vals_1458_, v_i_1460_, v_entries_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1463_, lean_object* v_depth_1464_, lean_object* v_keys_1465_, lean_object* v_vals_1466_, lean_object* v_heq_1467_, lean_object* v_i_1468_, lean_object* v_entries_1469_){
_start:
{
size_t v_depth_boxed_1470_; lean_object* v_res_1471_; 
v_depth_boxed_1470_ = lean_unbox_usize(v_depth_1464_);
lean_dec(v_depth_1464_);
v_res_1471_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__2(v_00_u03b2_1463_, v_depth_boxed_1470_, v_keys_1465_, v_vals_1466_, v_heq_1467_, v_i_1468_, v_entries_1469_);
lean_dec_ref(v_vals_1466_);
lean_dec_ref(v_keys_1465_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Ext_ExtTheorems_eraseCore_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1473_, v_x_1474_, v_x_1475_, v_x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(lean_object* v_declName_1478_, lean_object* v_as_1479_, size_t v_i_1480_, size_t v_stop_1481_, uint8_t v_b_1482_){
_start:
{
uint8_t v___y_1484_; uint8_t v___x_1488_; 
v___x_1488_ = lean_usize_dec_eq(v_i_1480_, v_stop_1481_);
if (v___x_1488_ == 0)
{
if (v_b_1482_ == 0)
{
lean_object* v___x_1489_; lean_object* v_declName_1490_; uint8_t v___x_1491_; 
v___x_1489_ = lean_array_uget_borrowed(v_as_1479_, v_i_1480_);
v_declName_1490_ = lean_ctor_get(v___x_1489_, 0);
v___x_1491_ = lean_name_eq(v_declName_1490_, v_declName_1478_);
v___y_1484_ = v___x_1491_;
goto v___jp_1483_;
}
else
{
v___y_1484_ = v_b_1482_;
goto v___jp_1483_;
}
}
else
{
return v_b_1482_;
}
v___jp_1483_:
{
size_t v___x_1485_; size_t v___x_1486_; 
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = lean_usize_add(v_i_1480_, v___x_1485_);
v_i_1480_ = v___x_1486_;
v_b_1482_ = v___y_1484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1___boxed(lean_object* v_declName_1492_, lean_object* v_as_1493_, lean_object* v_i_1494_, lean_object* v_stop_1495_, lean_object* v_b_1496_){
_start:
{
size_t v_i_boxed_1497_; size_t v_stop_boxed_1498_; uint8_t v_b_boxed_1499_; uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_i_boxed_1497_ = lean_unbox_usize(v_i_1494_);
lean_dec(v_i_1494_);
v_stop_boxed_1498_ = lean_unbox_usize(v_stop_1495_);
lean_dec(v_stop_1495_);
v_b_boxed_1499_ = lean_unbox(v_b_1496_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(v_declName_1492_, v_as_1493_, v_i_boxed_1497_, v_stop_boxed_1498_, v_b_boxed_1499_);
lean_dec_ref(v_as_1493_);
lean_dec(v_declName_1492_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(lean_object* v_declName_1502_, uint8_t v_x_1503_, lean_object* v_x_1504_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 0)
{
lean_object* v_child_1505_; 
v_child_1505_ = lean_ctor_get(v_x_1504_, 1);
v_x_1504_ = v_child_1505_;
goto _start;
}
else
{
lean_object* v_vs_1507_; lean_object* v_children_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_vs_1507_ = lean_ctor_get(v_x_1504_, 0);
v_children_1508_ = lean_ctor_get(v_x_1504_, 1);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_get_size(v_vs_1507_);
v___x_1511_ = lean_nat_dec_lt(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = lean_array_get_size(v_children_1508_);
v___x_1513_ = lean_nat_dec_lt(v___x_1509_, v___x_1512_);
if (v___x_1513_ == 0)
{
return v_x_1503_;
}
else
{
size_t v___x_1514_; size_t v___x_1515_; uint8_t v___x_1516_; 
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = lean_usize_of_nat(v___x_1512_);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_declName_1502_, v_children_1508_, v___x_1514_, v___x_1515_, v_x_1503_);
return v___x_1516_;
}
}
else
{
size_t v___x_1517_; size_t v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = lean_usize_of_nat(v___x_1510_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__1(v_declName_1502_, v_vs_1507_, v___x_1517_, v___x_1518_, v_x_1503_);
v___x_1520_ = lean_array_get_size(v_children_1508_);
v___x_1521_ = lean_nat_dec_lt(v___x_1509_, v___x_1520_);
if (v___x_1521_ == 0)
{
return v___x_1519_;
}
else
{
size_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = lean_usize_of_nat(v___x_1520_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_declName_1502_, v_children_1508_, v___x_1517_, v___x_1522_, v___x_1519_);
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(lean_object* v_declName_1524_, lean_object* v_as_1525_, size_t v_i_1526_, size_t v_stop_1527_, uint8_t v_b_1528_){
_start:
{
uint8_t v___x_1529_; 
v___x_1529_ = lean_usize_dec_eq(v_i_1526_, v_stop_1527_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v_snd_1531_; uint8_t v___x_1532_; size_t v___x_1533_; size_t v___x_1534_; 
v___x_1530_ = lean_array_uget_borrowed(v_as_1525_, v_i_1526_);
v_snd_1531_ = lean_ctor_get(v___x_1530_, 1);
v___x_1532_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(v_declName_1524_, v_b_1528_, v_snd_1531_);
v___x_1533_ = ((size_t)1ULL);
v___x_1534_ = lean_usize_add(v_i_1526_, v___x_1533_);
v_i_1526_ = v___x_1534_;
v_b_1528_ = v___x_1532_;
goto _start;
}
else
{
return v_b_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0___boxed(lean_object* v_declName_1536_, lean_object* v_as_1537_, lean_object* v_i_1538_, lean_object* v_stop_1539_, lean_object* v_b_1540_){
_start:
{
size_t v_i_boxed_1541_; size_t v_stop_boxed_1542_; uint8_t v_b_boxed_1543_; uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_i_boxed_1541_ = lean_unbox_usize(v_i_1538_);
lean_dec(v_i_1538_);
v_stop_boxed_1542_ = lean_unbox_usize(v_stop_1539_);
lean_dec(v_stop_1539_);
v_b_boxed_1543_ = lean_unbox(v_b_1540_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0_spec__0(v_declName_1536_, v_as_1537_, v_i_boxed_1541_, v_stop_boxed_1542_, v_b_boxed_1543_);
lean_dec_ref(v_as_1537_);
lean_dec(v_declName_1536_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0___boxed(lean_object* v_declName_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
uint8_t v_x_1092__boxed_1549_; uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_x_1092__boxed_1549_ = lean_unbox(v_x_1547_);
v_res_1550_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(v_declName_1546_, v_x_1092__boxed_1549_, v_x_1548_);
lean_dec_ref(v_x_1548_);
lean_dec(v_declName_1546_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(lean_object* v_declName_1552_, uint8_t v_s_1553_, lean_object* v_x_1554_, lean_object* v_t_1555_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__0(v_declName_1552_, v_s_1553_, v_t_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed(lean_object* v_declName_1557_, lean_object* v_s_1558_, lean_object* v_x_1559_, lean_object* v_t_1560_){
_start:
{
uint8_t v_s_boxed_1561_; uint8_t v_res_1562_; lean_object* v_r_1563_; 
v_s_boxed_1561_ = lean_unbox(v_s_1558_);
v_res_1562_ = l_Lean_Meta_Ext_ExtTheorems_contains___lam__0(v_declName_1557_, v_s_boxed_1561_, v_x_1559_, v_t_1560_);
lean_dec_ref(v_t_1560_);
lean_dec(v_x_1559_);
lean_dec(v_declName_1557_);
v_r_1563_ = lean_box(v_res_1562_);
return v_r_1563_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(lean_object* v_keys_1564_, lean_object* v_i_1565_, lean_object* v_k_1566_){
_start:
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = lean_array_get_size(v_keys_1564_);
v___x_1568_ = lean_nat_dec_lt(v_i_1565_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_dec(v_i_1565_);
return v___x_1568_;
}
else
{
lean_object* v_k_x27_1569_; uint8_t v___x_1570_; 
v_k_x27_1569_ = lean_array_fget_borrowed(v_keys_1564_, v_i_1565_);
v___x_1570_ = lean_name_eq(v_k_1566_, v_k_x27_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_unsigned_to_nat(1u);
v___x_1572_ = lean_nat_add(v_i_1565_, v___x_1571_);
lean_dec(v_i_1565_);
v_i_1565_ = v___x_1572_;
goto _start;
}
else
{
lean_dec(v_i_1565_);
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_keys_1574_, lean_object* v_i_1575_, lean_object* v_k_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1574_, v_i_1575_, v_k_1576_);
lean_dec(v_k_1576_);
lean_dec_ref(v_keys_1574_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(lean_object* v_x_1579_, size_t v_x_1580_, lean_object* v_x_1581_){
_start:
{
if (lean_obj_tag(v_x_1579_) == 0)
{
lean_object* v_es_1582_; lean_object* v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; lean_object* v_j_1586_; lean_object* v___x_1587_; 
v_es_1582_ = lean_ctor_get(v_x_1579_, 0);
v___x_1583_ = lean_box(2);
v___x_1584_ = ((size_t)31ULL);
v___x_1585_ = lean_usize_land(v_x_1580_, v___x_1584_);
v_j_1586_ = lean_usize_to_nat(v___x_1585_);
v___x_1587_ = lean_array_get_borrowed(v___x_1583_, v_es_1582_, v_j_1586_);
lean_dec(v_j_1586_);
switch(lean_obj_tag(v___x_1587_))
{
case 0:
{
lean_object* v_key_1588_; uint8_t v___x_1589_; 
v_key_1588_ = lean_ctor_get(v___x_1587_, 0);
v___x_1589_ = lean_name_eq(v_x_1581_, v_key_1588_);
return v___x_1589_;
}
case 1:
{
lean_object* v_node_1590_; size_t v___x_1591_; size_t v___x_1592_; 
v_node_1590_ = lean_ctor_get(v___x_1587_, 0);
v___x_1591_ = ((size_t)5ULL);
v___x_1592_ = lean_usize_shift_right(v_x_1580_, v___x_1591_);
v_x_1579_ = v_node_1590_;
v_x_1580_ = v___x_1592_;
goto _start;
}
default: 
{
uint8_t v___x_1594_; 
v___x_1594_ = 0;
return v___x_1594_;
}
}
}
else
{
lean_object* v_ks_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_ks_1595_ = lean_ctor_get(v_x_1579_, 0);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_ks_1595_, v___x_1596_, v_x_1581_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg___boxed(lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_){
_start:
{
size_t v_x_1162__boxed_1601_; uint8_t v_res_1602_; lean_object* v_r_1603_; 
v_x_1162__boxed_1601_ = lean_unbox_usize(v_x_1599_);
lean_dec(v_x_1599_);
v_res_1602_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1598_, v_x_1162__boxed_1601_, v_x_1600_);
lean_dec(v_x_1600_);
lean_dec_ref(v_x_1598_);
v_r_1603_ = lean_box(v_res_1602_);
return v_r_1603_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
uint64_t v___y_1607_; 
if (lean_obj_tag(v_x_1605_) == 0)
{
uint64_t v___x_1610_; 
v___x_1610_ = 1723ULL;
v___y_1607_ = v___x_1610_;
goto v___jp_1606_;
}
else
{
uint64_t v_hash_1611_; 
v_hash_1611_ = lean_ctor_get_uint64(v_x_1605_, sizeof(void*)*2);
v___y_1607_ = v_hash_1611_;
goto v___jp_1606_;
}
v___jp_1606_:
{
size_t v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = lean_uint64_to_usize(v___y_1607_);
v___x_1609_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1604_, v___x_1608_, v_x_1605_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg___boxed(lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1612_, v_x_1613_);
lean_dec(v_x_1613_);
lean_dec_ref(v_x_1612_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(lean_object* v_f_1616_, lean_object* v_keys_1617_, lean_object* v_vals_1618_, lean_object* v_i_1619_, lean_object* v_acc_1620_){
_start:
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = lean_array_get_size(v_keys_1617_);
v___x_1622_ = lean_nat_dec_lt(v_i_1619_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_dec(v_i_1619_);
lean_dec(v_f_1616_);
return v_acc_1620_;
}
else
{
lean_object* v_k_1623_; lean_object* v_v_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_k_1623_ = lean_array_fget_borrowed(v_keys_1617_, v_i_1619_);
v_v_1624_ = lean_array_fget_borrowed(v_vals_1618_, v_i_1619_);
lean_inc(v_f_1616_);
lean_inc(v_v_1624_);
lean_inc(v_k_1623_);
v___x_1625_ = lean_apply_3(v_f_1616_, v_acc_1620_, v_k_1623_, v_v_1624_);
v___x_1626_ = lean_unsigned_to_nat(1u);
v___x_1627_ = lean_nat_add(v_i_1619_, v___x_1626_);
lean_dec(v_i_1619_);
v_i_1619_ = v___x_1627_;
v_acc_1620_ = v___x_1625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_1629_, lean_object* v_keys_1630_, lean_object* v_vals_1631_, lean_object* v_i_1632_, lean_object* v_acc_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1629_, v_keys_1630_, v_vals_1631_, v_i_1632_, v_acc_1633_);
lean_dec_ref(v_vals_1631_);
lean_dec_ref(v_keys_1630_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1635_, lean_object* v_as_1636_, size_t v_i_1637_, size_t v_stop_1638_, lean_object* v_b_1639_){
_start:
{
lean_object* v___y_1641_; uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_eq(v_i_1637_, v_stop_1638_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_array_uget_borrowed(v_as_1636_, v_i_1637_);
switch(lean_obj_tag(v___x_1646_))
{
case 0:
{
lean_object* v_key_1647_; lean_object* v_val_1648_; lean_object* v___x_1649_; 
v_key_1647_ = lean_ctor_get(v___x_1646_, 0);
v_val_1648_ = lean_ctor_get(v___x_1646_, 1);
lean_inc(v_f_1635_);
lean_inc(v_val_1648_);
lean_inc(v_key_1647_);
v___x_1649_ = lean_apply_3(v_f_1635_, v_b_1639_, v_key_1647_, v_val_1648_);
v___y_1641_ = v___x_1649_;
goto v___jp_1640_;
}
case 1:
{
lean_object* v_node_1650_; lean_object* v___x_1651_; 
v_node_1650_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_f_1635_);
v___x_1651_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1635_, v_node_1650_, v_b_1639_);
v___y_1641_ = v___x_1651_;
goto v___jp_1640_;
}
default: 
{
v___y_1641_ = v_b_1639_;
goto v___jp_1640_;
}
}
}
else
{
lean_dec(v_f_1635_);
return v_b_1639_;
}
v___jp_1640_:
{
size_t v___x_1642_; size_t v___x_1643_; 
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_add(v_i_1637_, v___x_1642_);
v_i_1637_ = v___x_1643_;
v_b_1639_ = v___y_1641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(lean_object* v_f_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
if (lean_obj_tag(v_x_1653_) == 0)
{
lean_object* v_es_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_es_1655_ = lean_ctor_get(v_x_1653_, 0);
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = lean_array_get_size(v_es_1655_);
v___x_1658_ = lean_nat_dec_lt(v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_dec(v_f_1652_);
return v_x_1654_;
}
else
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = lean_usize_of_nat(v___x_1657_);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1652_, v_es_1655_, v___x_1659_, v___x_1660_, v_x_1654_);
return v___x_1661_;
}
}
else
{
lean_object* v_ks_1662_; lean_object* v_vs_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_ks_1662_ = lean_ctor_get(v_x_1653_, 0);
v_vs_1663_ = lean_ctor_get(v_x_1653_, 1);
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1652_, v_ks_1662_, v_vs_1663_, v___x_1664_, v_x_1654_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg___boxed(lean_object* v_f_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1666_, v_x_1667_, v_x_1668_);
lean_dec_ref(v_x_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1670_, lean_object* v_as_1671_, lean_object* v_i_1672_, lean_object* v_stop_1673_, lean_object* v_b_1674_){
_start:
{
size_t v_i_boxed_1675_; size_t v_stop_boxed_1676_; lean_object* v_res_1677_; 
v_i_boxed_1675_ = lean_unbox_usize(v_i_1672_);
lean_dec(v_i_1672_);
v_stop_boxed_1676_ = lean_unbox_usize(v_stop_1673_);
lean_dec(v_stop_1673_);
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1670_, v_as_1671_, v_i_boxed_1675_, v_stop_boxed_1676_, v_b_1674_);
lean_dec_ref(v_as_1671_);
return v_res_1677_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object* v_d_1678_, lean_object* v_declName_1679_){
_start:
{
lean_object* v_tree_1680_; lean_object* v_erased_1681_; lean_object* v___f_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_tree_1680_ = lean_ctor_get(v_d_1678_, 0);
v_erased_1681_ = lean_ctor_get(v_d_1678_, 1);
lean_inc(v_declName_1679_);
v___f_1682_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1682_, 0, v_declName_1679_);
v___x_1683_ = 0;
v___x_1684_ = lean_box(v___x_1683_);
v___x_1685_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v___f_1682_, v_tree_1680_, v___x_1684_);
v___x_1686_ = lean_unbox(v___x_1685_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
lean_dec(v_declName_1679_);
v___x_1687_ = lean_unbox(v___x_1685_);
lean_dec(v___x_1685_);
return v___x_1687_;
}
else
{
uint8_t v___x_1688_; 
v___x_1688_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_erased_1681_, v_declName_1679_);
lean_dec(v_declName_1679_);
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_unbox(v___x_1685_);
lean_dec(v___x_1685_);
return v___x_1689_;
}
else
{
lean_dec(v___x_1685_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object* v_d_1690_, lean_object* v_declName_1691_){
_start:
{
uint8_t v_res_1692_; lean_object* v_r_1693_; 
v_res_1692_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1690_, v_declName_1691_);
lean_dec_ref(v_d_1690_);
v_r_1693_ = lean_box(v_res_1692_);
return v_r_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(lean_object* v_map_1694_, lean_object* v_f_1695_, lean_object* v_init_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1695_, v_map_1694_, v_init_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg___boxed(lean_object* v_map_1698_, lean_object* v_f_1699_, lean_object* v_init_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___redArg(v_map_1698_, v_f_1699_, v_init_1700_);
lean_dec_ref(v_map_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(lean_object* v_00_u03c3_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_map_1704_, lean_object* v_f_1705_, lean_object* v_init_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1705_, v_map_1704_, v_init_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1___boxed(lean_object* v_00_u03c3_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_map_1710_, lean_object* v_f_1711_, lean_object* v_init_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1(v_00_u03c3_1708_, v_00_u03b2_1709_, v_map_1710_, v_f_1711_, v_init_1712_);
lean_dec_ref(v_map_1710_);
return v_res_1713_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(lean_object* v_00_u03b2_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___redArg(v_x_1715_, v_x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2___boxed(lean_object* v_00_u03b2_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
uint8_t v_res_1721_; lean_object* v_r_1722_; 
v_res_1721_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2(v_00_u03b2_1718_, v_x_1719_, v_x_1720_);
lean_dec(v_x_1720_);
lean_dec_ref(v_x_1719_);
v_r_1722_ = lean_box(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(lean_object* v_00_u03c3_1723_, lean_object* v_00_u03b1_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_f_1726_, lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___redArg(v_f_1726_, v_x_1727_, v_x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1730_, lean_object* v_00_u03b1_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_f_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3(v_00_u03c3_1730_, v_00_u03b1_1731_, v_00_u03b2_1732_, v_f_1733_, v_x_1734_, v_x_1735_);
lean_dec_ref(v_x_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(lean_object* v_00_u03b2_1737_, lean_object* v_x_1738_, size_t v_x_1739_, lean_object* v_x_1740_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___redArg(v_x_1738_, v_x_1739_, v_x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
size_t v_x_1319__boxed_1746_; uint8_t v_res_1747_; lean_object* v_r_1748_; 
v_x_1319__boxed_1746_ = lean_unbox_usize(v_x_1744_);
lean_dec(v_x_1744_);
v_res_1747_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5(v_00_u03b2_1742_, v_x_1743_, v_x_1319__boxed_1746_, v_x_1745_);
lean_dec(v_x_1745_);
lean_dec_ref(v_x_1743_);
v_r_1748_ = lean_box(v_res_1747_);
return v_r_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_00_u03c3_1751_, lean_object* v_f_1752_, lean_object* v_as_1753_, size_t v_i_1754_, size_t v_stop_1755_, lean_object* v_b_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___redArg(v_f_1752_, v_as_1753_, v_i_1754_, v_stop_1755_, v_b_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_00_u03c3_1760_, lean_object* v_f_1761_, lean_object* v_as_1762_, lean_object* v_i_1763_, lean_object* v_stop_1764_, lean_object* v_b_1765_){
_start:
{
size_t v_i_boxed_1766_; size_t v_stop_boxed_1767_; lean_object* v_res_1768_; 
v_i_boxed_1766_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_stop_boxed_1767_ = lean_unbox_usize(v_stop_1764_);
lean_dec(v_stop_1764_);
v_res_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__4(v_00_u03b1_1758_, v_00_u03b2_1759_, v_00_u03c3_1760_, v_f_1761_, v_as_1762_, v_i_boxed_1766_, v_stop_boxed_1767_, v_b_1765_);
lean_dec_ref(v_as_1762_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1769_, lean_object* v_00_u03b1_1770_, lean_object* v_00_u03b2_1771_, lean_object* v_f_1772_, lean_object* v_keys_1773_, lean_object* v_vals_1774_, lean_object* v_heq_1775_, lean_object* v_i_1776_, lean_object* v_acc_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___redArg(v_f_1772_, v_keys_1773_, v_vals_1774_, v_i_1776_, v_acc_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1779_, lean_object* v_00_u03b1_1780_, lean_object* v_00_u03b2_1781_, lean_object* v_f_1782_, lean_object* v_keys_1783_, lean_object* v_vals_1784_, lean_object* v_heq_1785_, lean_object* v_i_1786_, lean_object* v_acc_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__1_spec__3_spec__5(v_00_u03c3_1779_, v_00_u03b1_1780_, v_00_u03b2_1781_, v_f_1782_, v_keys_1783_, v_vals_1784_, v_heq_1785_, v_i_1786_, v_acc_1787_);
lean_dec_ref(v_vals_1784_);
lean_dec_ref(v_keys_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1789_, lean_object* v_keys_1790_, lean_object* v_vals_1791_, lean_object* v_heq_1792_, lean_object* v_i_1793_, lean_object* v_k_1794_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___redArg(v_keys_1790_, v_i_1793_, v_k_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1796_, lean_object* v_keys_1797_, lean_object* v_vals_1798_, lean_object* v_heq_1799_, lean_object* v_i_1800_, lean_object* v_k_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Ext_ExtTheorems_contains_spec__2_spec__5_spec__8(v_00_u03b2_1796_, v_keys_1797_, v_vals_1798_, v_heq_1799_, v_i_1800_, v_k_1801_);
lean_dec(v_k_1801_);
lean_dec_ref(v_vals_1798_);
lean_dec_ref(v_keys_1797_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg(lean_object* v_declName_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v_env_1809_; lean_object* v___x_1810_; lean_object* v_ext_1811_; lean_object* v_toEnvExtension_1812_; lean_object* v_asyncMode_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1807_ = l_Lean_Meta_Ext_instInhabitedExtTheorems_default;
v___x_1808_ = lean_st_ref_get(v_a_1805_);
v_env_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_ref(v_env_1809_);
lean_dec(v___x_1808_);
v___x_1810_ = l_Lean_Meta_Ext_extExtension;
v_ext_1811_ = lean_ctor_get(v___x_1810_, 1);
v_toEnvExtension_1812_ = lean_ctor_get(v_ext_1811_, 0);
v_asyncMode_1813_ = lean_ctor_get(v_toEnvExtension_1812_, 2);
v___x_1814_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1807_, v___x_1810_, v_env_1809_, v_asyncMode_1813_);
v___x_1815_ = l_Lean_Meta_Ext_ExtTheorems_contains(v___x_1814_, v_declName_1804_);
lean_dec(v___x_1814_);
v___x_1816_ = lean_box(v___x_1815_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___redArg___boxed(lean_object* v_declName_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1818_, v_a_1819_);
lean_dec(v_a_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object* v_declName_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Meta_Ext_isExtTheorem___redArg(v_declName_1822_, v_a_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object* v_declName_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Meta_Ext_isExtTheorem(v_declName_1827_, v_a_1828_, v_a_1829_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(lean_object* v_d_1832_, lean_object* v_declName_1833_, lean_object* v_toPure_1834_, lean_object* v_____r_1835_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = l_Lean_Meta_Ext_ExtTheorems_eraseCore(v_d_1832_, v_declName_1833_);
v___x_1837_ = lean_apply_2(v_toPure_1834_, lean_box(0), v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1(lean_object* v___f_1838_, lean_object* v_____r_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_apply_1(v___f_1838_, v_____r_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__0));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__2));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___redArg(lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_d_1849_, lean_object* v_declName_1850_){
_start:
{
lean_object* v_toApplicative_1851_; lean_object* v_toBind_1852_; lean_object* v_toPure_1853_; lean_object* v___f_1854_; uint8_t v___x_1855_; 
v_toApplicative_1851_ = lean_ctor_get(v_inst_1847_, 0);
v_toBind_1852_ = lean_ctor_get(v_inst_1847_, 1);
lean_inc(v_toBind_1852_);
v_toPure_1853_ = lean_ctor_get(v_toApplicative_1851_, 1);
lean_inc(v_toPure_1853_);
lean_inc_n(v_declName_1850_, 2);
lean_inc_ref(v_d_1849_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1854_, 0, v_d_1849_);
lean_closure_set(v___f_1854_, 1, v_declName_1850_);
lean_closure_set(v___f_1854_, 2, v_toPure_1853_);
v___x_1855_ = l_Lean_Meta_Ext_ExtTheorems_contains(v_d_1849_, v_declName_1850_);
if (v___x_1855_ == 0)
{
lean_object* v___f_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec_ref(v_d_1849_);
v___f_1856_ = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1856_, 0, v___f_1854_);
v___x_1857_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__1);
v___x_1858_ = l_Lean_MessageData_ofConstName(v_declName_1850_, v___x_1855_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_obj_once(&l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3, &l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3_once, _init_l_Lean_Meta_Ext_ExtTheorems_erase___redArg___closed__3);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_throwError___redArg(v_inst_1847_, v_inst_1848_, v___x_1861_);
v___x_1863_ = lean_apply_4(v_toBind_1852_, lean_box(0), lean_box(0), v___x_1862_, v___f_1856_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_inc(v_toPure_1853_);
lean_dec_ref(v___f_1854_);
lean_dec(v_toBind_1852_);
lean_dec_ref(v_inst_1848_);
lean_dec_ref(v_inst_1847_);
v___x_1864_ = lean_box(0);
v___x_1865_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg___lam__0(v_d_1849_, v_declName_1850_, v_toPure_1853_, v___x_1864_);
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object* v_m_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_d_1869_, lean_object* v_declName_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Meta_Ext_ExtTheorems_erase___redArg(v_inst_1867_, v_inst_1868_, v_d_1869_, v_declName_1870_);
return v___x_1871_;
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
