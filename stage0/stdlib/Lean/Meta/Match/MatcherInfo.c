// Lean compiler output
// Module: Lean.Meta.Match.MatcherInfo
// Imports: public import Lean.Meta.Basic
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedDiscrInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedDiscrInfo;
static const lean_string_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hName\?"};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprDiscrInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprDiscrInfo = (const lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedOverlaps_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedOverlaps;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5_value;
static const lean_string_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7;
static lean_once_cell_t l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__6_value)}};
static const lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10 = (const lean_object*)&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeSet.ofList "};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__3_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprOverlaps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprOverlaps_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprOverlaps___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprOverlaps = (const lean_object*)&l_Lean_Meta_Match_instReprOverlaps___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_isEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_Overlaps_overlapping___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Overlaps_overlapping___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo = (const lean_object*)&l_Lean_Meta_Match_instInhabitedAltParamInfo_default___closed__0_value;
static const lean_string_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "numOverlaps"};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "hasUnitThunk"};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprAltParamInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprAltParamInfo = (const lean_object*)&l_Lean_Meta_Match_instReprAltParamInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instBEqAltParamInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instBEqAltParamInfo = (const lean_object*)&l_Lean_Meta_Match_instBEqAltParamInfo___closed__0_value;
static const lean_array_object l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instInhabitedMatcherInfo;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(lean_object*);
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numDiscrs"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "altInfos"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "uElimPos\?"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__9_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "discrInfos"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13;
static const lean_string_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "overlaps"};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Match_instReprMatcherInfo___closed__0 = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Match_instReprMatcherInfo = (const lean_object*)&l_Lean_Meta_Match_instReprMatcherInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object*);
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__1;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__2;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__3;
static lean_once_cell_t l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_switch(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "extension"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 134, 186, 123, 61, 240, 95, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 199, 90, 164, 66, 112, 193, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 71, 76, 183, 128, 212, 252, 252)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_Extension_State_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_extension;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfoCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "matcherLikeExt"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 239, 16, 207, 7, 86, 101, 26)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matcherLikeExt;
LEAN_EXPORT lean_object* l_Lean_Meta_markMatcherLike(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherLikeCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLikeCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedDiscrInfo(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
if (lean_obj_tag(v_x_9_) == 0)
{
lean_object* v___x_11_; 
v___x_11_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1));
return v___x_11_;
}
else
{
lean_object* v_val_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_val_12_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_val_12_);
lean_dec_ref_known(v_x_9_, 1);
v___x_13_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3));
v___x_14_ = lean_unsigned_to_nat(1024u);
v___x_15_ = l_Lean_Name_reprPrec(v_val_12_, v___x_14_);
v___x_16_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_13_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = l_Repr_addAppParen(v___x_16_, v_x_10_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___boxed(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(v_x_18_, v_x_19_);
lean_dec(v_x_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__1(lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_nat_to_int(v_a_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(10u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__0));
v___x_40_ = lean_string_length(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__9);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(lean_object* v_x_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_48_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__6));
v___x_49_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__7);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0(v_x_47_, v___x_50_);
v___x_52_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_49_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = 0;
v___x_54_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*1, v___x_53_);
v___x_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_48_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_57_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_55_);
v___x_59_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_56_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*1, v___x_53_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr(lean_object* v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprDiscrInfo_repr___boxed(lean_object* v_x_66_, lean_object* v_prec_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_Match_instReprDiscrInfo_repr(v_x_66_, v_prec_67_);
lean_dec(v_prec_67_);
return v_res_68_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_box(0);
v___x_72_ = lean_unsigned_to_nat(16u);
v___x_73_ = lean_mk_array(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0, &l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0_once, _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__0);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps_default(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1, &l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedOverlaps_default___closed__1);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedOverlaps(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_inc(v_x_79_);
return v_x_79_;
}
else
{
lean_object* v_key_81_; lean_object* v_value_82_; lean_object* v_tail_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_key_81_ = lean_ctor_get(v_x_80_, 0);
v_value_82_ = lean_ctor_get(v_x_80_, 1);
v_tail_83_ = lean_ctor_get(v_x_80_, 2);
v___x_84_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_79_, v_tail_83_);
lean_inc(v_value_82_);
lean_inc(v_key_81_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_key_81_);
lean_ctor_set(v___x_85_, 1, v_value_82_);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_x_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec(v_x_87_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(lean_object* v_as_90_, size_t v_i_91_, size_t v_stop_92_, lean_object* v_b_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = lean_usize_dec_eq(v_i_91_, v_stop_92_);
if (v___x_94_ == 0)
{
size_t v___x_95_; size_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_sub(v_i_91_, v___x_95_);
v___x_97_ = lean_array_uget_borrowed(v_as_90_, v___x_96_);
v___x_98_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__1(v_b_93_, v___x_97_);
lean_dec(v_b_93_);
v_i_91_ = v___x_96_;
v_b_93_ = v___x_98_;
goto _start;
}
else
{
return v_b_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2___boxed(lean_object* v_as_100_, lean_object* v_i_101_, lean_object* v_stop_102_, lean_object* v_b_103_){
_start:
{
size_t v_i_boxed_104_; size_t v_stop_boxed_105_; lean_object* v_res_106_; 
v_i_boxed_104_ = lean_unbox_usize(v_i_101_);
lean_dec(v_i_101_);
v_stop_boxed_105_ = lean_unbox_usize(v_stop_102_);
lean_dec(v_stop_102_);
v_res_106_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_as_100_, v_i_boxed_104_, v_stop_boxed_105_, v_b_103_);
lean_dec_ref(v_as_100_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_dec(v_x_107_);
return v_x_108_;
}
else
{
lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
v_head_110_ = lean_ctor_get(v_x_109_, 0);
v_tail_111_ = lean_ctor_get(v_x_109_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_109_);
if (v_isSharedCheck_122_ == 0)
{
v___x_113_ = v_x_109_;
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_tail_111_);
lean_inc(v_head_110_);
lean_dec(v_x_109_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
lean_inc(v_x_107_);
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 5);
lean_ctor_set(v___x_113_, 1, v_x_107_);
lean_ctor_set(v___x_113_, 0, v_x_108_);
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_108_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_x_107_);
v___x_116_ = v_reuseFailAlloc_121_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = l_Nat_reprFast(v_head_110_);
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v_x_108_ = v___x_119_;
v_x_109_ = v_tail_111_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_dec(v_x_123_);
return v_x_124_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_138_; 
v_head_126_ = lean_ctor_get(v_x_125_, 0);
v_tail_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_138_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_head_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
lean_inc(v_x_123_);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 5);
lean_ctor_set(v___x_129_, 1, v_x_123_);
lean_ctor_set(v___x_129_, 0, v_x_124_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_x_124_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_x_123_);
v___x_132_ = v_reuseFailAlloc_137_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = l_Nat_reprFast(v_head_126_);
v___x_134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_132_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(v_x_123_, v___x_135_, v_tail_127_);
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = l_Nat_reprFast(v___y_139_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_144_; 
lean_dec(v_x_143_);
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
lean_object* v_tail_145_; 
v_tail_145_ = lean_ctor_get(v_x_142_, 1);
if (lean_obj_tag(v_tail_145_) == 0)
{
lean_object* v_head_146_; lean_object* v___x_147_; 
lean_dec(v_x_143_);
v_head_146_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_head_146_);
lean_dec_ref_known(v_x_142_, 2);
v___x_147_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_146_);
return v___x_147_;
}
else
{
lean_object* v_head_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc(v_tail_145_);
v_head_148_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_head_148_);
lean_dec_ref_known(v_x_142_, 2);
v___x_149_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_148_);
v___x_150_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(v_x_143_, v___x_149_, v_tail_145_);
return v___x_150_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_163_ = lean_string_length(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_a_170_){
_start:
{
if (lean_obj_tag(v_a_170_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1));
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; 
v___x_172_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_173_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(v_a_170_, v___x_172_);
v___x_174_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
v___x_175_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9));
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_173_);
v___x_177_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_174_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*1, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_dec(v_x_182_);
return v_x_183_;
}
else
{
lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
v_head_185_ = lean_ctor_get(v_x_184_, 0);
v_tail_186_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v_x_184_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_tail_186_);
lean_inc(v_head_185_);
lean_dec(v_x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
lean_inc(v_x_182_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 5);
lean_ctor_set(v___x_188_, 1, v_x_182_);
lean_ctor_set(v___x_188_, 0, v_x_183_);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_x_183_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_x_182_);
v___x_191_ = v_reuseFailAlloc_194_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_head_185_);
v_x_183_ = v___x_192_;
v_x_184_ = v_tail_186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v___x_198_; 
lean_dec(v_x_197_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v_tail_199_; 
v_tail_199_ = lean_ctor_get(v_x_196_, 1);
if (lean_obj_tag(v_tail_199_) == 0)
{
lean_object* v_head_200_; 
lean_dec(v_x_197_);
v_head_200_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_head_200_);
lean_dec_ref_known(v_x_196_, 2);
return v_head_200_;
}
else
{
lean_object* v_head_201_; lean_object* v___x_202_; 
lean_inc(v_tail_199_);
v_head_201_ = lean_ctor_get(v_x_196_, 0);
lean_inc(v_head_201_);
lean_dec_ref_known(v_x_196_, 2);
v___x_202_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(v_x_197_, v_head_201_, v_tail_199_);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(lean_object* v_init_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v_k_205_; lean_object* v_l_206_; lean_object* v_r_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_k_205_ = lean_ctor_get(v_x_204_, 1);
v_l_206_ = lean_ctor_get(v_x_204_, 3);
v_r_207_ = lean_ctor_get(v_x_204_, 4);
v___x_208_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_203_, v_r_207_);
lean_inc(v_k_205_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v_k_205_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v_init_203_ = v___x_209_;
v_x_204_ = v_l_206_;
goto _start;
}
else
{
return v_init_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_init_211_, lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_211_, v_x_212_);
lean_dec(v_x_212_);
return v_res_213_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0));
v___x_220_ = lean_string_length(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(lean_object* v_x_227_){
_start:
{
lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_257_; 
v_fst_228_ = lean_ctor_get(v_x_227_, 0);
v_snd_229_ = lean_ctor_get(v_x_227_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_257_ == 0)
{
v___x_231_ = v_x_227_;
v_isShared_232_ = v_isSharedCheck_257_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_snd_229_);
lean_inc(v_fst_228_);
lean_dec(v_x_227_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_257_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_233_ = l_Nat_reprFast(v_fst_228_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = lean_box(0);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 1);
lean_ctor_set(v___x_231_, 1, v___x_235_);
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_237_ = v___x_231_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_235_);
v___x_237_ = v_reuseFailAlloc_256_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2));
v___x_240_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v___x_235_, v_snd_229_);
lean_dec(v_snd_229_);
v___x_241_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v___x_240_);
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v___x_238_);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_237_);
v___x_245_ = l_List_reverse___redArg(v___x_244_);
v___x_246_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_247_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(v___x_245_, v___x_246_);
v___x_248_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5);
v___x_249_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6));
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_247_);
v___x_251_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7));
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_248_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = 0;
v___x_255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_dec(v_x_258_);
return v_x_259_;
}
else
{
lean_object* v_head_261_; lean_object* v_tail_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_272_; 
v_head_261_ = lean_ctor_get(v_x_260_, 0);
v_tail_262_ = lean_ctor_get(v_x_260_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_272_ == 0)
{
v___x_264_ = v_x_260_;
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_tail_262_);
lean_inc(v_head_261_);
lean_dec(v_x_260_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_272_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
lean_inc(v_x_258_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 5);
lean_ctor_set(v___x_264_, 1, v_x_258_);
lean_ctor_set(v___x_264_, 0, v_x_259_);
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_x_259_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_x_258_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_261_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v_x_259_ = v___x_269_;
v_x_260_ = v_tail_262_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_dec(v_x_273_);
return v_x_274_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_287_; 
v_head_276_ = lean_ctor_get(v_x_275_, 0);
v_tail_277_ = lean_ctor_get(v_x_275_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_287_ == 0)
{
v___x_279_ = v_x_275_;
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_tail_277_);
lean_inc(v_head_276_);
lean_dec(v_x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_287_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
lean_inc(v_x_273_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 5);
lean_ctor_set(v___x_279_, 1, v_x_273_);
lean_ctor_set(v___x_279_, 0, v_x_274_);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_x_274_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_x_273_);
v___x_282_ = v_reuseFailAlloc_286_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_276_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(v_x_273_, v___x_284_, v_tail_277_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_288_) == 0)
{
lean_object* v___x_290_; 
lean_dec(v_x_289_);
v___x_290_ = lean_box(0);
return v___x_290_;
}
else
{
lean_object* v_tail_291_; 
v_tail_291_ = lean_ctor_get(v_x_288_, 1);
if (lean_obj_tag(v_tail_291_) == 0)
{
lean_object* v_head_292_; lean_object* v___x_293_; 
lean_dec(v_x_289_);
v_head_292_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_head_292_);
lean_dec_ref_known(v_x_288_, 2);
v___x_293_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_292_);
return v___x_293_;
}
else
{
lean_object* v_head_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_inc(v_tail_291_);
v_head_294_ = lean_ctor_get(v_x_288_, 0);
lean_inc(v_head_294_);
lean_dec_ref_known(v_x_288_, 2);
v___x_295_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_294_);
v___x_296_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(v_x_289_, v___x_295_, v_tail_291_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(lean_object* v_a_297_){
_start:
{
if (lean_obj_tag(v_a_297_) == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1));
return v___x_298_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; 
v___x_299_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_300_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(v_a_297_, v___x_299_);
v___x_301_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
v___x_302_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9));
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_300_);
v___x_304_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_301_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = 0;
v___x_308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_307_);
return v___x_308_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(7u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg(lean_object* v_x_323_){
_start:
{
lean_object* v_buckets_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_356_; 
v_buckets_324_ = lean_ctor_get(v_x_323_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v_x_323_, 0);
lean_dec(v_unused_357_);
v___x_326_ = v_x_323_;
v_isShared_327_ = v_isSharedCheck_356_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_buckets_324_);
lean_dec(v_x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_356_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___y_333_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_328_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3));
v___x_329_ = lean_obj_once(&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6));
v___x_350_ = lean_box(0);
v___x_351_ = lean_array_get_size(v_buckets_324_);
v___x_352_ = lean_nat_dec_lt(v___x_330_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec_ref(v_buckets_324_);
v___y_333_ = v___x_350_;
goto v___jp_332_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_usize_of_nat(v___x_351_);
v___x_354_ = ((size_t)0ULL);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_buckets_324_, v___x_353_, v___x_354_, v___x_350_);
lean_dec_ref(v_buckets_324_);
v___y_333_ = v___x_355_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v___y_333_);
if (v_isShared_327_ == 0)
{
lean_ctor_set_tag(v___x_326_, 5);
lean_ctor_set(v___x_326_, 1, v___x_334_);
lean_ctor_set(v___x_326_, 0, v___x_331_);
v___x_336_ = v___x_326_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_349_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_337_ = l_Repr_addAppParen(v___x_336_, v___x_330_);
v___x_338_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_329_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = 0;
v___x_340_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_339_);
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_328_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_343_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_341_);
v___x_345_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_342_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*1, v___x_339_);
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr(lean_object* v_x_358_, lean_object* v_prec_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_x_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___boxed(lean_object* v_x_361_, lean_object* v_prec_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Match_instReprOverlaps_repr(v_x_361_, v_prec_362_);
lean_dec(v_prec_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(lean_object* v_a_364_, lean_object* v_n_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v_a_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(lean_object* v_a_367_, lean_object* v_n_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_a_367_, v_n_368_);
lean_dec(v_n_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_x_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___boxed(lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(v_x_373_, v_x_374_);
lean_dec(v_x_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(lean_object* v_a_376_, lean_object* v_n_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v_a_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_a_379_, lean_object* v_n_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(v_a_379_, v_n_380_);
lean_dec(v_n_380_);
return v_res_381_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object* v_o_384_){
_start:
{
lean_object* v_size_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_size_385_ = lean_ctor_get(v_o_384_, 0);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = lean_nat_dec_eq(v_size_385_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_isEmpty___boxed(lean_object* v_o_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_o_388_);
lean_dec_ref(v_o_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(lean_object* v_k_391_, lean_object* v_t_392_){
_start:
{
if (lean_obj_tag(v_t_392_) == 0)
{
lean_object* v_k_393_; lean_object* v_l_394_; lean_object* v_r_395_; uint8_t v___x_396_; 
v_k_393_ = lean_ctor_get(v_t_392_, 1);
v_l_394_ = lean_ctor_get(v_t_392_, 3);
v_r_395_ = lean_ctor_get(v_t_392_, 4);
v___x_396_ = lean_nat_dec_lt(v_k_391_, v_k_393_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_eq(v_k_391_, v_k_393_);
if (v___x_397_ == 0)
{
v_t_392_ = v_r_395_;
goto _start;
}
else
{
return v___x_397_;
}
}
else
{
v_t_392_ = v_l_394_;
goto _start;
}
}
else
{
uint8_t v___x_400_; 
v___x_400_ = 0;
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(lean_object* v_k_401_, lean_object* v_t_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_401_, v_t_402_);
lean_dec(v_t_402_);
lean_dec(v_k_401_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(lean_object* v_k_405_, lean_object* v_v_406_, lean_object* v_t_407_){
_start:
{
if (lean_obj_tag(v_t_407_) == 0)
{
lean_object* v_size_408_; lean_object* v_k_409_; lean_object* v_v_410_; lean_object* v_l_411_; lean_object* v_r_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_693_; 
v_size_408_ = lean_ctor_get(v_t_407_, 0);
v_k_409_ = lean_ctor_get(v_t_407_, 1);
v_v_410_ = lean_ctor_get(v_t_407_, 2);
v_l_411_ = lean_ctor_get(v_t_407_, 3);
v_r_412_ = lean_ctor_get(v_t_407_, 4);
v_isSharedCheck_693_ = !lean_is_exclusive(v_t_407_);
if (v_isSharedCheck_693_ == 0)
{
v___x_414_ = v_t_407_;
v_isShared_415_ = v_isSharedCheck_693_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_r_412_);
lean_inc(v_l_411_);
lean_inc(v_v_410_);
lean_inc(v_k_409_);
lean_inc(v_size_408_);
lean_dec(v_t_407_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_693_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; 
v___x_416_ = lean_nat_dec_lt(v_k_405_, v_k_409_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
v___x_417_ = lean_nat_dec_eq(v_k_405_, v_k_409_);
if (v___x_417_ == 0)
{
lean_object* v_impl_418_; lean_object* v___x_419_; 
lean_dec(v_size_408_);
v_impl_418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_405_, v_v_406_, v_r_412_);
v___x_419_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_411_) == 0)
{
lean_object* v_size_420_; lean_object* v_size_421_; lean_object* v_k_422_; lean_object* v_v_423_; lean_object* v_l_424_; lean_object* v_r_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_size_420_ = lean_ctor_get(v_l_411_, 0);
v_size_421_ = lean_ctor_get(v_impl_418_, 0);
lean_inc(v_size_421_);
v_k_422_ = lean_ctor_get(v_impl_418_, 1);
lean_inc(v_k_422_);
v_v_423_ = lean_ctor_get(v_impl_418_, 2);
lean_inc(v_v_423_);
v_l_424_ = lean_ctor_get(v_impl_418_, 3);
lean_inc(v_l_424_);
v_r_425_ = lean_ctor_get(v_impl_418_, 4);
lean_inc(v_r_425_);
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = lean_nat_mul(v___x_426_, v_size_420_);
v___x_428_ = lean_nat_dec_lt(v___x_427_, v_size_421_);
lean_dec(v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec(v_r_425_);
lean_dec(v_l_424_);
lean_dec(v_v_423_);
lean_dec(v_k_422_);
v___x_429_ = lean_nat_add(v___x_419_, v_size_420_);
v___x_430_ = lean_nat_add(v___x_429_, v_size_421_);
lean_dec(v_size_421_);
lean_dec(v___x_429_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_impl_418_);
lean_ctor_set(v___x_414_, 0, v___x_430_);
v___x_432_ = v___x_414_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_impl_418_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_497_; 
v_isSharedCheck_497_ = !lean_is_exclusive(v_impl_418_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; lean_object* v_unused_500_; lean_object* v_unused_501_; lean_object* v_unused_502_; 
v_unused_498_ = lean_ctor_get(v_impl_418_, 4);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_impl_418_, 3);
lean_dec(v_unused_499_);
v_unused_500_ = lean_ctor_get(v_impl_418_, 2);
lean_dec(v_unused_500_);
v_unused_501_ = lean_ctor_get(v_impl_418_, 1);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_impl_418_, 0);
lean_dec(v_unused_502_);
v___x_435_ = v_impl_418_;
v_isShared_436_ = v_isSharedCheck_497_;
goto v_resetjp_434_;
}
else
{
lean_dec(v_impl_418_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_497_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_size_437_; lean_object* v_k_438_; lean_object* v_v_439_; lean_object* v_l_440_; lean_object* v_r_441_; lean_object* v_size_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_size_437_ = lean_ctor_get(v_l_424_, 0);
v_k_438_ = lean_ctor_get(v_l_424_, 1);
v_v_439_ = lean_ctor_get(v_l_424_, 2);
v_l_440_ = lean_ctor_get(v_l_424_, 3);
v_r_441_ = lean_ctor_get(v_l_424_, 4);
v_size_442_ = lean_ctor_get(v_r_425_, 0);
v___x_443_ = lean_unsigned_to_nat(2u);
v___x_444_ = lean_nat_mul(v___x_443_, v_size_442_);
v___x_445_ = lean_nat_dec_lt(v_size_437_, v___x_444_);
lean_dec(v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_473_; 
lean_inc(v_r_441_);
lean_inc(v_l_440_);
lean_inc(v_v_439_);
lean_inc(v_k_438_);
v_isSharedCheck_473_ = !lean_is_exclusive(v_l_424_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_474_ = lean_ctor_get(v_l_424_, 4);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_l_424_, 3);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_l_424_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_l_424_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_l_424_, 0);
lean_dec(v_unused_478_);
v___x_447_ = v_l_424_;
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
else
{
lean_dec(v_l_424_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_473_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_463_; 
v___x_449_ = lean_nat_add(v___x_419_, v_size_420_);
v___x_450_ = lean_nat_add(v___x_449_, v_size_421_);
lean_dec(v_size_421_);
if (lean_obj_tag(v_l_440_) == 0)
{
lean_object* v_size_471_; 
v_size_471_ = lean_ctor_get(v_l_440_, 0);
lean_inc(v_size_471_);
v___y_463_ = v_size_471_;
goto v___jp_462_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___y_463_ = v___x_472_;
goto v___jp_462_;
}
v___jp_451_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_nat_add(v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec(v___y_453_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 4, v_r_425_);
lean_ctor_set(v___x_447_, 3, v_r_441_);
lean_ctor_set(v___x_447_, 2, v_v_423_);
lean_ctor_set(v___x_447_, 1, v_k_422_);
lean_ctor_set(v___x_447_, 0, v___x_455_);
v___x_457_ = v___x_447_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_k_422_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_v_423_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_r_441_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_r_425_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v___x_457_);
lean_ctor_set(v___x_435_, 3, v___y_452_);
lean_ctor_set(v___x_435_, 2, v_v_439_);
lean_ctor_set(v___x_435_, 1, v_k_438_);
lean_ctor_set(v___x_435_, 0, v___x_450_);
v___x_459_ = v___x_435_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_k_438_);
lean_ctor_set(v_reuseFailAlloc_460_, 2, v_v_439_);
lean_ctor_set(v_reuseFailAlloc_460_, 3, v___y_452_);
lean_ctor_set(v_reuseFailAlloc_460_, 4, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
v___jp_462_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_nat_add(v___x_449_, v___y_463_);
lean_dec(v___y_463_);
lean_dec(v___x_449_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_l_440_);
lean_ctor_set(v___x_414_, 0, v___x_464_);
v___x_466_ = v___x_414_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v_l_440_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_nat_add(v___x_419_, v_size_442_);
if (lean_obj_tag(v_r_441_) == 0)
{
lean_object* v_size_468_; 
v_size_468_ = lean_ctor_get(v_r_441_, 0);
lean_inc(v_size_468_);
v___y_452_ = v___x_466_;
v___y_453_ = v___x_467_;
v___y_454_ = v_size_468_;
goto v___jp_451_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___y_452_ = v___x_466_;
v___y_453_ = v___x_467_;
v___y_454_ = v___x_469_;
goto v___jp_451_;
}
}
}
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
lean_del_object(v___x_414_);
v___x_479_ = lean_nat_add(v___x_419_, v_size_420_);
v___x_480_ = lean_nat_add(v___x_479_, v_size_421_);
lean_dec(v_size_421_);
v___x_481_ = lean_nat_add(v___x_479_, v_size_437_);
lean_dec(v___x_479_);
lean_inc_ref(v_l_411_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v_l_424_);
lean_ctor_set(v___x_435_, 3, v_l_411_);
lean_ctor_set(v___x_435_, 2, v_v_410_);
lean_ctor_set(v___x_435_, 1, v_k_409_);
lean_ctor_set(v___x_435_, 0, v___x_481_);
v___x_483_ = v___x_435_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_l_424_);
v___x_483_ = v_reuseFailAlloc_496_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_isSharedCheck_490_ = !lean_is_exclusive(v_l_411_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; lean_object* v_unused_492_; lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_491_ = lean_ctor_get(v_l_411_, 4);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_l_411_, 3);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_l_411_, 2);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_l_411_, 1);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_l_411_, 0);
lean_dec(v_unused_495_);
v___x_485_ = v_l_411_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_dec(v_l_411_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 4, v_r_425_);
lean_ctor_set(v___x_485_, 3, v___x_483_);
lean_ctor_set(v___x_485_, 2, v_v_423_);
lean_ctor_set(v___x_485_, 1, v_k_422_);
lean_ctor_set(v___x_485_, 0, v___x_480_);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_422_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_423_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v_r_425_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_503_; 
v_l_503_ = lean_ctor_get(v_impl_418_, 3);
lean_inc(v_l_503_);
if (lean_obj_tag(v_l_503_) == 0)
{
lean_object* v_r_504_; lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_529_; 
v_r_504_ = lean_ctor_get(v_impl_418_, 4);
v_k_505_ = lean_ctor_get(v_impl_418_, 1);
v_v_506_ = lean_ctor_get(v_impl_418_, 2);
v_isSharedCheck_529_ = !lean_is_exclusive(v_impl_418_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_530_ = lean_ctor_get(v_impl_418_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_impl_418_, 0);
lean_dec(v_unused_531_);
v___x_508_ = v_impl_418_;
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_r_504_);
lean_inc(v_v_506_);
lean_inc(v_k_505_);
lean_dec(v_impl_418_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_529_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_k_510_; lean_object* v_v_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_525_; 
v_k_510_ = lean_ctor_get(v_l_503_, 1);
v_v_511_ = lean_ctor_get(v_l_503_, 2);
v_isSharedCheck_525_ = !lean_is_exclusive(v_l_503_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; lean_object* v_unused_528_; 
v_unused_526_ = lean_ctor_get(v_l_503_, 4);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_l_503_, 3);
lean_dec(v_unused_527_);
v_unused_528_ = lean_ctor_get(v_l_503_, 0);
lean_dec(v_unused_528_);
v___x_513_ = v_l_503_;
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_v_511_);
lean_inc(v_k_510_);
lean_dec(v_l_503_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_525_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_504_, 2);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 4, v_r_504_);
lean_ctor_set(v___x_513_, 3, v_r_504_);
lean_ctor_set(v___x_513_, 2, v_v_410_);
lean_ctor_set(v___x_513_, 1, v_k_409_);
lean_ctor_set(v___x_513_, 0, v___x_419_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_r_504_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_r_504_);
v___x_517_ = v_reuseFailAlloc_524_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
lean_inc(v_r_504_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 3, v_r_504_);
lean_ctor_set(v___x_508_, 0, v___x_419_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_k_505_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_v_506_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_r_504_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_r_504_);
v___x_519_ = v_reuseFailAlloc_523_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_519_);
lean_ctor_set(v___x_414_, 3, v___x_517_);
lean_ctor_set(v___x_414_, 2, v_v_511_);
lean_ctor_set(v___x_414_, 1, v_k_510_);
lean_ctor_set(v___x_414_, 0, v___x_515_);
v___x_521_ = v___x_414_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_510_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
else
{
lean_object* v_r_532_; 
v_r_532_ = lean_ctor_get(v_impl_418_, 4);
lean_inc(v_r_532_);
if (lean_obj_tag(v_r_532_) == 0)
{
lean_object* v_k_533_; lean_object* v_v_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
v_k_533_ = lean_ctor_get(v_impl_418_, 1);
v_v_534_ = lean_ctor_get(v_impl_418_, 2);
v_isSharedCheck_545_ = !lean_is_exclusive(v_impl_418_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; lean_object* v_unused_548_; 
v_unused_546_ = lean_ctor_get(v_impl_418_, 4);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_impl_418_, 3);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_impl_418_, 0);
lean_dec(v_unused_548_);
v___x_536_ = v_impl_418_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_v_534_);
lean_inc(v_k_533_);
lean_dec(v_impl_418_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(3u);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 4, v_l_503_);
lean_ctor_set(v___x_536_, 2, v_v_410_);
lean_ctor_set(v___x_536_, 1, v_k_409_);
lean_ctor_set(v___x_536_, 0, v___x_419_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v_l_503_);
lean_ctor_set(v_reuseFailAlloc_544_, 4, v_l_503_);
v___x_540_ = v_reuseFailAlloc_544_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_r_532_);
lean_ctor_set(v___x_414_, 3, v___x_540_);
lean_ctor_set(v___x_414_, 2, v_v_534_);
lean_ctor_set(v___x_414_, 1, v_k_533_);
lean_ctor_set(v___x_414_, 0, v___x_538_);
v___x_542_ = v___x_414_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_r_532_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(2u);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_impl_418_);
lean_ctor_set(v___x_414_, 3, v_r_532_);
lean_ctor_set(v___x_414_, 0, v___x_549_);
v___x_551_ = v___x_414_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_r_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_impl_418_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
else
{
lean_object* v___x_554_; 
lean_dec(v_v_410_);
lean_dec(v_k_409_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 2, v_v_406_);
lean_ctor_set(v___x_414_, 1, v_k_405_);
v___x_554_ = v___x_414_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_size_408_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_405_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_406_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_l_411_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_r_412_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v_impl_556_; lean_object* v___x_557_; 
lean_dec(v_size_408_);
v_impl_556_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_405_, v_v_406_, v_l_411_);
v___x_557_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_412_) == 0)
{
lean_object* v_size_558_; lean_object* v_size_559_; lean_object* v_k_560_; lean_object* v_v_561_; lean_object* v_l_562_; lean_object* v_r_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_size_558_ = lean_ctor_get(v_r_412_, 0);
v_size_559_ = lean_ctor_get(v_impl_556_, 0);
lean_inc(v_size_559_);
v_k_560_ = lean_ctor_get(v_impl_556_, 1);
lean_inc(v_k_560_);
v_v_561_ = lean_ctor_get(v_impl_556_, 2);
lean_inc(v_v_561_);
v_l_562_ = lean_ctor_get(v_impl_556_, 3);
lean_inc(v_l_562_);
v_r_563_ = lean_ctor_get(v_impl_556_, 4);
lean_inc(v_r_563_);
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = lean_nat_mul(v___x_564_, v_size_558_);
v___x_566_ = lean_nat_dec_lt(v___x_565_, v_size_559_);
lean_dec(v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
lean_dec(v_r_563_);
lean_dec(v_l_562_);
lean_dec(v_v_561_);
lean_dec(v_k_560_);
v___x_567_ = lean_nat_add(v___x_557_, v_size_559_);
lean_dec(v_size_559_);
v___x_568_ = lean_nat_add(v___x_567_, v_size_558_);
lean_dec(v___x_567_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 3, v_impl_556_);
lean_ctor_set(v___x_414_, 0, v___x_568_);
v___x_570_ = v___x_414_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_impl_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_r_412_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_637_; 
v_isSharedCheck_637_ = !lean_is_exclusive(v_impl_556_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_638_ = lean_ctor_get(v_impl_556_, 4);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_impl_556_, 3);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_impl_556_, 2);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_impl_556_, 1);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_impl_556_, 0);
lean_dec(v_unused_642_);
v___x_573_ = v_impl_556_;
v_isShared_574_ = v_isSharedCheck_637_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_impl_556_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_637_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_size_575_; lean_object* v_size_576_; lean_object* v_k_577_; lean_object* v_v_578_; lean_object* v_l_579_; lean_object* v_r_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_size_575_ = lean_ctor_get(v_l_562_, 0);
v_size_576_ = lean_ctor_get(v_r_563_, 0);
v_k_577_ = lean_ctor_get(v_r_563_, 1);
v_v_578_ = lean_ctor_get(v_r_563_, 2);
v_l_579_ = lean_ctor_get(v_r_563_, 3);
v_r_580_ = lean_ctor_get(v_r_563_, 4);
v___x_581_ = lean_unsigned_to_nat(2u);
v___x_582_ = lean_nat_mul(v___x_581_, v_size_575_);
v___x_583_ = lean_nat_dec_lt(v_size_576_, v___x_582_);
lean_dec(v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_612_; 
lean_inc(v_r_580_);
lean_inc(v_l_579_);
lean_inc(v_v_578_);
lean_inc(v_k_577_);
v_isSharedCheck_612_ = !lean_is_exclusive(v_r_563_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; lean_object* v_unused_616_; lean_object* v_unused_617_; 
v_unused_613_ = lean_ctor_get(v_r_563_, 4);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_r_563_, 3);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_r_563_, 2);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_r_563_, 1);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_r_563_, 0);
lean_dec(v_unused_617_);
v___x_585_ = v_r_563_;
v_isShared_586_ = v_isSharedCheck_612_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_r_563_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_612_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___x_600_; lean_object* v___y_602_; 
v___x_587_ = lean_nat_add(v___x_557_, v_size_559_);
lean_dec(v_size_559_);
v___x_588_ = lean_nat_add(v___x_587_, v_size_558_);
lean_dec(v___x_587_);
v___x_600_ = lean_nat_add(v___x_557_, v_size_575_);
if (lean_obj_tag(v_l_579_) == 0)
{
lean_object* v_size_610_; 
v_size_610_ = lean_ctor_get(v_l_579_, 0);
lean_inc(v_size_610_);
v___y_602_ = v_size_610_;
goto v___jp_601_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___y_602_ = v___x_611_;
goto v___jp_601_;
}
v___jp_589_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_nat_add(v___y_590_, v___y_592_);
lean_dec(v___y_592_);
lean_dec(v___y_590_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v_r_412_);
lean_ctor_set(v___x_585_, 3, v_r_580_);
lean_ctor_set(v___x_585_, 2, v_v_410_);
lean_ctor_set(v___x_585_, 1, v_k_409_);
lean_ctor_set(v___x_585_, 0, v___x_593_);
v___x_595_ = v___x_585_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_r_580_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_r_412_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 4, v___x_595_);
lean_ctor_set(v___x_573_, 3, v___y_591_);
lean_ctor_set(v___x_573_, 2, v_v_578_);
lean_ctor_set(v___x_573_, 1, v_k_577_);
lean_ctor_set(v___x_573_, 0, v___x_588_);
v___x_597_ = v___x_573_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_k_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_v_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v___y_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
v___jp_601_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_nat_add(v___x_600_, v___y_602_);
lean_dec(v___y_602_);
lean_dec(v___x_600_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_l_579_);
lean_ctor_set(v___x_414_, 3, v_l_562_);
lean_ctor_set(v___x_414_, 2, v_v_561_);
lean_ctor_set(v___x_414_, 1, v_k_560_);
lean_ctor_set(v___x_414_, 0, v___x_603_);
v___x_605_ = v___x_414_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_l_579_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_nat_add(v___x_557_, v_size_558_);
if (lean_obj_tag(v_r_580_) == 0)
{
lean_object* v_size_607_; 
v_size_607_ = lean_ctor_get(v_r_580_, 0);
lean_inc(v_size_607_);
v___y_590_ = v___x_606_;
v___y_591_ = v___x_605_;
v___y_592_ = v_size_607_;
goto v___jp_589_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___y_590_ = v___x_606_;
v___y_591_ = v___x_605_;
v___y_592_ = v___x_608_;
goto v___jp_589_;
}
}
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
lean_del_object(v___x_414_);
v___x_618_ = lean_nat_add(v___x_557_, v_size_559_);
lean_dec(v_size_559_);
v___x_619_ = lean_nat_add(v___x_618_, v_size_558_);
lean_dec(v___x_618_);
v___x_620_ = lean_nat_add(v___x_557_, v_size_558_);
v___x_621_ = lean_nat_add(v___x_620_, v_size_576_);
lean_dec(v___x_620_);
lean_inc_ref(v_r_412_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 4, v_r_412_);
lean_ctor_set(v___x_573_, 3, v_r_563_);
lean_ctor_set(v___x_573_, 2, v_v_410_);
lean_ctor_set(v___x_573_, 1, v_k_409_);
lean_ctor_set(v___x_573_, 0, v___x_621_);
v___x_623_ = v___x_573_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_r_563_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_r_412_);
v___x_623_ = v_reuseFailAlloc_636_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v_r_412_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; lean_object* v_unused_632_; lean_object* v_unused_633_; lean_object* v_unused_634_; lean_object* v_unused_635_; 
v_unused_631_ = lean_ctor_get(v_r_412_, 4);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_r_412_, 3);
lean_dec(v_unused_632_);
v_unused_633_ = lean_ctor_get(v_r_412_, 2);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_r_412_, 1);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_r_412_, 0);
lean_dec(v_unused_635_);
v___x_625_ = v_r_412_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_dec(v_r_412_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 4, v___x_623_);
lean_ctor_set(v___x_625_, 3, v_l_562_);
lean_ctor_set(v___x_625_, 2, v_v_561_);
lean_ctor_set(v___x_625_, 1, v_k_560_);
lean_ctor_set(v___x_625_, 0, v___x_619_);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_k_560_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_v_561_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v___x_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_643_; 
v_l_643_ = lean_ctor_get(v_impl_556_, 3);
lean_inc(v_l_643_);
if (lean_obj_tag(v_l_643_) == 0)
{
lean_object* v_r_644_; lean_object* v_k_645_; lean_object* v_v_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_657_; 
v_r_644_ = lean_ctor_get(v_impl_556_, 4);
v_k_645_ = lean_ctor_get(v_impl_556_, 1);
v_v_646_ = lean_ctor_get(v_impl_556_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_impl_556_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; 
v_unused_658_ = lean_ctor_get(v_impl_556_, 3);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_impl_556_, 0);
lean_dec(v_unused_659_);
v___x_648_ = v_impl_556_;
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_r_644_);
lean_inc(v_v_646_);
lean_inc(v_k_645_);
lean_dec(v_impl_556_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_657_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 3, v_r_644_);
lean_ctor_set(v___x_648_, 2, v_v_410_);
lean_ctor_set(v___x_648_, 1, v_k_409_);
lean_ctor_set(v___x_648_, 0, v___x_557_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_r_644_);
lean_ctor_set(v_reuseFailAlloc_656_, 4, v_r_644_);
v___x_652_ = v_reuseFailAlloc_656_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_654_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_652_);
lean_ctor_set(v___x_414_, 3, v_l_643_);
lean_ctor_set(v___x_414_, 2, v_v_646_);
lean_ctor_set(v___x_414_, 1, v_k_645_);
lean_ctor_set(v___x_414_, 0, v___x_650_);
v___x_654_ = v___x_414_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_645_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_646_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_l_643_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_r_660_; 
v_r_660_ = lean_ctor_get(v_impl_556_, 4);
lean_inc(v_r_660_);
if (lean_obj_tag(v_r_660_) == 0)
{
lean_object* v_k_661_; lean_object* v_v_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_685_; 
v_k_661_ = lean_ctor_get(v_impl_556_, 1);
v_v_662_ = lean_ctor_get(v_impl_556_, 2);
v_isSharedCheck_685_ = !lean_is_exclusive(v_impl_556_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; lean_object* v_unused_687_; lean_object* v_unused_688_; 
v_unused_686_ = lean_ctor_get(v_impl_556_, 4);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_impl_556_, 3);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_impl_556_, 0);
lean_dec(v_unused_688_);
v___x_664_ = v_impl_556_;
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_v_662_);
lean_inc(v_k_661_);
lean_dec(v_impl_556_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_k_666_; lean_object* v_v_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_681_; 
v_k_666_ = lean_ctor_get(v_r_660_, 1);
v_v_667_ = lean_ctor_get(v_r_660_, 2);
v_isSharedCheck_681_ = !lean_is_exclusive(v_r_660_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; 
v_unused_682_ = lean_ctor_get(v_r_660_, 4);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_r_660_, 3);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_r_660_, 0);
lean_dec(v_unused_684_);
v___x_669_ = v_r_660_;
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_v_667_);
lean_inc(v_k_666_);
lean_dec(v_r_660_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_681_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(3u);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_l_643_);
lean_ctor_set(v___x_669_, 3, v_l_643_);
lean_ctor_set(v___x_669_, 2, v_v_662_);
lean_ctor_set(v___x_669_, 1, v_k_661_);
lean_ctor_set(v___x_669_, 0, v___x_557_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_k_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_v_662_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_l_643_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_l_643_);
v___x_673_ = v_reuseFailAlloc_680_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_l_643_);
lean_ctor_set(v___x_664_, 2, v_v_410_);
lean_ctor_set(v___x_664_, 1, v_k_409_);
lean_ctor_set(v___x_664_, 0, v___x_557_);
v___x_675_ = v___x_664_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_l_643_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_l_643_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v___x_675_);
lean_ctor_set(v___x_414_, 3, v___x_673_);
lean_ctor_set(v___x_414_, 2, v_v_667_);
lean_ctor_set(v___x_414_, 1, v_k_666_);
lean_ctor_set(v___x_414_, 0, v___x_671_);
v___x_677_ = v___x_414_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_unsigned_to_nat(2u);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_r_660_);
lean_ctor_set(v___x_414_, 3, v_impl_556_);
lean_ctor_set(v___x_414_, 0, v___x_689_);
v___x_691_ = v___x_414_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_409_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_410_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_impl_556_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_r_660_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_k_405_);
lean_ctor_set(v___x_695_, 2, v_v_406_);
lean_ctor_set(v___x_695_, 3, v_t_407_);
lean_ctor_set(v___x_695_, 4, v_t_407_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(lean_object* v_overlapping_696_, lean_object* v_s_x3f_697_){
_start:
{
lean_object* v___y_699_; 
if (lean_obj_tag(v_s_x3f_697_) == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_box(1);
v___y_699_ = v___x_705_;
goto v___jp_698_;
}
else
{
lean_object* v_val_706_; 
v_val_706_ = lean_ctor_get(v_s_x3f_697_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_s_x3f_697_, 1);
v___y_699_ = v_val_706_;
goto v___jp_698_;
}
v___jp_698_:
{
uint8_t v___x_700_; 
v___x_700_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_696_, v___y_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
v___x_702_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_696_, v___x_701_, v___y_699_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec(v_overlapping_696_);
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___y_699_);
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(lean_object* v_overlapping_707_, lean_object* v_a_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_val_712_; lean_object* v___x_713_; 
v___x_710_ = lean_box(0);
v___x_711_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_707_, v___x_710_);
v_val_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_val_712_);
lean_dec(v___x_711_);
v___x_713_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_713_, 0, v_a_708_);
lean_ctor_set(v___x_713_, 1, v_val_712_);
lean_ctor_set(v___x_713_, 2, v_x_709_);
return v___x_713_;
}
else
{
lean_object* v_key_714_; lean_object* v_value_715_; lean_object* v_tail_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_731_; 
v_key_714_ = lean_ctor_get(v_x_709_, 0);
v_value_715_ = lean_ctor_get(v_x_709_, 1);
v_tail_716_ = lean_ctor_get(v_x_709_, 2);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_731_ == 0)
{
v___x_718_ = v_x_709_;
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_tail_716_);
lean_inc(v_value_715_);
lean_inc(v_key_714_);
lean_dec(v_x_709_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_eq(v_key_714_, v_a_708_);
if (v___x_720_ == 0)
{
lean_object* v_tail_721_; lean_object* v___x_723_; 
v_tail_721_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_707_, v_a_708_, v_tail_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v_tail_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_key_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_value_715_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_tail_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_val_727_; lean_object* v___x_729_; 
lean_dec(v_key_714_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_value_715_);
v___x_726_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_707_, v___x_725_);
v_val_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_727_);
lean_dec(v___x_726_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v_val_727_);
lean_ctor_set(v___x_718_, 0, v_a_708_);
v___x_729_ = v___x_718_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_708_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_val_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_tail_716_);
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
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(lean_object* v_a_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
else
{
lean_object* v_key_735_; lean_object* v_tail_736_; uint8_t v___x_737_; 
v_key_735_ = lean_ctor_get(v_x_733_, 0);
v_tail_736_ = lean_ctor_get(v_x_733_, 2);
v___x_737_ = lean_nat_dec_eq(v_key_735_, v_a_732_);
if (v___x_737_ == 0)
{
v_x_733_ = v_tail_736_;
goto _start;
}
else
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(lean_object* v_a_739_, lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_739_, v_x_740_);
lean_dec(v_x_740_);
lean_dec(v_a_739_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
return v_x_743_;
}
else
{
lean_object* v_key_745_; lean_object* v_value_746_; lean_object* v_tail_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_770_; 
v_key_745_ = lean_ctor_get(v_x_744_, 0);
v_value_746_ = lean_ctor_get(v_x_744_, 1);
v_tail_747_ = lean_ctor_get(v_x_744_, 2);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_770_ == 0)
{
v___x_749_ = v_x_744_;
v_isShared_750_ = v_isSharedCheck_770_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_tail_747_);
lean_inc(v_value_746_);
lean_inc(v_key_745_);
lean_dec(v_x_744_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_770_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; uint64_t v___x_752_; uint64_t v___x_753_; uint64_t v___x_754_; uint64_t v_fold_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; size_t v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_751_ = lean_array_get_size(v_x_743_);
v___x_752_ = lean_uint64_of_nat(v_key_745_);
v___x_753_ = 32ULL;
v___x_754_ = lean_uint64_shift_right(v___x_752_, v___x_753_);
v_fold_755_ = lean_uint64_xor(v___x_752_, v___x_754_);
v___x_756_ = 16ULL;
v___x_757_ = lean_uint64_shift_right(v_fold_755_, v___x_756_);
v___x_758_ = lean_uint64_xor(v_fold_755_, v___x_757_);
v___x_759_ = lean_uint64_to_usize(v___x_758_);
v___x_760_ = lean_usize_of_nat(v___x_751_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_sub(v___x_760_, v___x_761_);
v___x_763_ = lean_usize_land(v___x_759_, v___x_762_);
v___x_764_ = lean_array_uget_borrowed(v_x_743_, v___x_763_);
lean_inc(v___x_764_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 2, v___x_764_);
v___x_766_ = v___x_749_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_key_745_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_value_746_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v___x_764_);
v___x_766_ = v_reuseFailAlloc_769_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; 
v___x_767_ = lean_array_uset(v_x_743_, v___x_763_, v___x_766_);
v_x_743_ = v___x_767_;
v_x_744_ = v_tail_747_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(lean_object* v_i_771_, lean_object* v_source_772_, lean_object* v_target_773_){
_start:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_source_772_);
v___x_775_ = lean_nat_dec_lt(v_i_771_, v___x_774_);
if (v___x_775_ == 0)
{
lean_dec_ref(v_source_772_);
lean_dec(v_i_771_);
return v_target_773_;
}
else
{
lean_object* v_es_776_; lean_object* v___x_777_; lean_object* v_source_778_; lean_object* v_target_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_es_776_ = lean_array_fget(v_source_772_, v_i_771_);
v___x_777_ = lean_box(0);
v_source_778_ = lean_array_fset(v_source_772_, v_i_771_, v___x_777_);
v_target_779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_target_773_, v_es_776_);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_i_771_, v___x_780_);
lean_dec(v_i_771_);
v_i_771_ = v___x_781_;
v_source_772_ = v_source_778_;
v_target_773_ = v_target_779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(lean_object* v_data_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_nbuckets_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_784_ = lean_array_get_size(v_data_783_);
v___x_785_ = lean_unsigned_to_nat(2u);
v_nbuckets_786_ = lean_nat_mul(v___x_784_, v___x_785_);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_box(0);
v___x_789_ = lean_mk_array(v_nbuckets_786_, v___x_788_);
v___x_790_ = lean_array_propagate_mark(v_data_783_, v___x_789_);
v___x_791_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v___x_787_, v_data_783_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(lean_object* v_overlapping_792_, lean_object* v_m_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_size_795_; lean_object* v_buckets_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_848_; 
v_size_795_ = lean_ctor_get(v_m_793_, 0);
v_buckets_796_ = lean_ctor_get(v_m_793_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_m_793_);
if (v_isSharedCheck_848_ == 0)
{
v___x_798_ = v_m_793_;
v_isShared_799_ = v_isSharedCheck_848_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_buckets_796_);
lean_inc(v_size_795_);
lean_dec(v_m_793_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_848_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; uint64_t v___x_801_; uint64_t v___x_802_; uint64_t v___x_803_; uint64_t v_fold_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; lean_object* v_bkt_813_; lean_object* v___y_815_; uint8_t v___x_833_; 
v___x_800_ = lean_array_get_size(v_buckets_796_);
v___x_801_ = lean_uint64_of_nat(v_a_794_);
v___x_802_ = 32ULL;
v___x_803_ = lean_uint64_shift_right(v___x_801_, v___x_802_);
v_fold_804_ = lean_uint64_xor(v___x_801_, v___x_803_);
v___x_805_ = 16ULL;
v___x_806_ = lean_uint64_shift_right(v_fold_804_, v___x_805_);
v___x_807_ = lean_uint64_xor(v_fold_804_, v___x_806_);
v___x_808_ = lean_uint64_to_usize(v___x_807_);
v___x_809_ = lean_usize_of_nat(v___x_800_);
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_sub(v___x_809_, v___x_810_);
v___x_812_ = lean_usize_land(v___x_808_, v___x_811_);
v_bkt_813_ = lean_array_uget_borrowed(v_buckets_796_, v___x_812_);
v___x_833_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_794_, v_bkt_813_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_box(1);
v___x_835_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_792_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_box(0);
v___x_837_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_792_, v___x_836_, v___x_834_);
v___y_815_ = v___x_837_;
goto v___jp_814_;
}
else
{
lean_dec(v_overlapping_792_);
v___y_815_ = v___x_834_;
goto v___jp_814_;
}
}
else
{
lean_object* v___x_838_; lean_object* v_buckets_x27_839_; lean_object* v_bkt_x27_840_; lean_object* v___y_842_; uint8_t v___x_845_; 
lean_inc(v_bkt_813_);
lean_del_object(v___x_798_);
v___x_838_ = lean_box(0);
v_buckets_x27_839_ = lean_array_uset(v_buckets_796_, v___x_812_, v___x_838_);
lean_inc(v_a_794_);
v_bkt_x27_840_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_792_, v_a_794_, v_bkt_813_);
v___x_845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_794_, v_bkt_x27_840_);
lean_dec(v_a_794_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_sub(v_size_795_, v___x_846_);
lean_dec(v_size_795_);
v___y_842_ = v___x_847_;
goto v___jp_841_;
}
else
{
v___y_842_ = v_size_795_;
goto v___jp_841_;
}
v___jp_841_:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_array_uset(v_buckets_x27_839_, v___x_812_, v_bkt_x27_840_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___y_842_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
return v___x_844_;
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v_size_x27_817_; lean_object* v___x_818_; lean_object* v_buckets_x27_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_816_ = lean_unsigned_to_nat(1u);
v_size_x27_817_ = lean_nat_add(v_size_795_, v___x_816_);
lean_dec(v_size_795_);
lean_inc(v_bkt_813_);
v___x_818_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_818_, 0, v_a_794_);
lean_ctor_set(v___x_818_, 1, v___y_815_);
lean_ctor_set(v___x_818_, 2, v_bkt_813_);
v_buckets_x27_819_ = lean_array_uset(v_buckets_796_, v___x_812_, v___x_818_);
v___x_820_ = lean_unsigned_to_nat(4u);
v___x_821_ = lean_nat_mul(v_size_x27_817_, v___x_820_);
v___x_822_ = lean_unsigned_to_nat(3u);
v___x_823_ = lean_nat_div(v___x_821_, v___x_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_array_get_size(v_buckets_x27_819_);
v___x_825_ = lean_nat_dec_le(v___x_823_, v___x_824_);
lean_dec(v___x_823_);
if (v___x_825_ == 0)
{
lean_object* v_val_826_; lean_object* v___x_828_; 
v_val_826_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_buckets_x27_819_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v_val_826_);
lean_ctor_set(v___x_798_, 0, v_size_x27_817_);
v___x_828_ = v___x_798_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_size_x27_817_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_val_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_object* v___x_831_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v_buckets_x27_819_);
lean_ctor_set(v___x_798_, 0, v_size_x27_817_);
v___x_831_ = v___x_798_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_size_x27_817_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_buckets_x27_819_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert(lean_object* v_o_849_, lean_object* v_overlapping_850_, lean_object* v_overlapped_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(v_overlapping_850_, v_o_849_, v_overlapped_851_);
return v___x_852_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_object* v_00_u03b2_853_, lean_object* v_k_854_, lean_object* v_t_855_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_854_, v_t_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(lean_object* v_00_u03b2_857_, lean_object* v_k_858_, lean_object* v_t_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(v_00_u03b2_857_, v_k_858_, v_t_859_);
lean_dec(v_t_859_);
lean_dec(v_k_858_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(lean_object* v_00_u03b2_862_, lean_object* v_k_863_, lean_object* v_v_864_, lean_object* v_t_865_, lean_object* v_hl_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_863_, v_v_864_, v_t_865_);
return v___x_867_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_object* v_00_u03b2_868_, lean_object* v_a_869_, lean_object* v_x_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(lean_object* v_00_u03b2_872_, lean_object* v_a_873_, lean_object* v_x_874_){
_start:
{
uint8_t v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(v_00_u03b2_872_, v_a_873_, v_x_874_);
lean_dec(v_x_874_);
lean_dec(v_a_873_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3(lean_object* v_00_u03b2_877_, lean_object* v_data_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_data_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_880_, lean_object* v_i_881_, lean_object* v_source_882_, lean_object* v_target_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v_i_881_, v_source_882_, v_target_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_x_886_, v_x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(lean_object* v_a_889_, lean_object* v_x_890_){
_start:
{
if (lean_obj_tag(v_x_890_) == 0)
{
lean_object* v___x_891_; 
v___x_891_ = lean_box(0);
return v___x_891_;
}
else
{
lean_object* v_key_892_; lean_object* v_value_893_; lean_object* v_tail_894_; uint8_t v___x_895_; 
v_key_892_ = lean_ctor_get(v_x_890_, 0);
v_value_893_ = lean_ctor_get(v_x_890_, 1);
v_tail_894_ = lean_ctor_get(v_x_890_, 2);
v___x_895_ = lean_nat_dec_eq(v_key_892_, v_a_889_);
if (v___x_895_ == 0)
{
v_x_890_ = v_tail_894_;
goto _start;
}
else
{
lean_object* v___x_897_; 
lean_inc(v_value_893_);
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_value_893_);
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(lean_object* v_a_898_, lean_object* v_x_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_898_, v_x_899_);
lean_dec(v_x_899_);
lean_dec(v_a_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(lean_object* v_m_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_buckets_903_; lean_object* v___x_904_; uint64_t v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v_fold_908_; uint64_t v___x_909_; uint64_t v___x_910_; uint64_t v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_buckets_903_ = lean_ctor_get(v_m_901_, 1);
v___x_904_ = lean_array_get_size(v_buckets_903_);
v___x_905_ = lean_uint64_of_nat(v_a_902_);
v___x_906_ = 32ULL;
v___x_907_ = lean_uint64_shift_right(v___x_905_, v___x_906_);
v_fold_908_ = lean_uint64_xor(v___x_905_, v___x_907_);
v___x_909_ = 16ULL;
v___x_910_ = lean_uint64_shift_right(v_fold_908_, v___x_909_);
v___x_911_ = lean_uint64_xor(v_fold_908_, v___x_910_);
v___x_912_ = lean_uint64_to_usize(v___x_911_);
v___x_913_ = lean_usize_of_nat(v___x_904_);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_sub(v___x_913_, v___x_914_);
v___x_916_ = lean_usize_land(v___x_912_, v___x_915_);
v___x_917_ = lean_array_uget_borrowed(v_buckets_903_, v___x_916_);
v___x_918_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_902_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg___boxed(lean_object* v_m_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_m_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(lean_object* v_init_922_, lean_object* v_x_923_){
_start:
{
if (lean_obj_tag(v_x_923_) == 0)
{
lean_object* v_k_924_; lean_object* v_l_925_; lean_object* v_r_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_k_924_ = lean_ctor_get(v_x_923_, 1);
lean_inc(v_k_924_);
v_l_925_ = lean_ctor_get(v_x_923_, 3);
lean_inc(v_l_925_);
v_r_926_ = lean_ctor_get(v_x_923_, 4);
lean_inc(v_r_926_);
lean_dec_ref_known(v_x_923_, 5);
v___x_927_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_922_, v_l_925_);
v___x_928_ = lean_array_push(v___x_927_, v_k_924_);
v_init_922_ = v___x_928_;
v_x_923_ = v_r_926_;
goto _start;
}
else
{
return v_init_922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object* v_o_932_, lean_object* v_overlapped_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_o_932_, v_overlapped_933_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v___x_935_; 
v___x_935_ = ((lean_object*)(l_Lean_Meta_Match_Overlaps_overlapping___closed__0));
return v___x_935_;
}
else
{
lean_object* v_val_936_; lean_object* v___y_938_; 
v_val_936_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_934_, 1);
if (lean_obj_tag(v_val_936_) == 0)
{
lean_object* v_size_941_; 
v_size_941_ = lean_ctor_get(v_val_936_, 0);
lean_inc(v_size_941_);
v___y_938_ = v_size_941_;
goto v___jp_937_;
}
else
{
lean_object* v___x_942_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___y_938_ = v___x_942_;
goto v___jp_937_;
}
v___jp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_mk_empty_array_with_capacity(v___y_938_);
lean_dec(v___y_938_);
v___x_940_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v___x_939_, v_val_936_);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping___boxed(lean_object* v_o_943_, lean_object* v_overlapped_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Match_Overlaps_overlapping(v_o_943_, v_overlapped_944_);
lean_dec(v_overlapped_944_);
lean_dec_ref(v_o_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(lean_object* v_00_u03b2_946_, lean_object* v_m_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_947_, v_a_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(lean_object* v_00_u03b2_950_, lean_object* v_m_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(v_00_u03b2_950_, v_m_951_, v_a_952_);
lean_dec(v_a_952_);
lean_dec_ref(v_m_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(lean_object* v_init_954_, lean_object* v_t_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_954_, v_t_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(lean_object* v_00_u03b2_957_, lean_object* v_a_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(lean_object* v_00_u03b2_961_, lean_object* v_a_962_, lean_object* v_x_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(v_00_u03b2_961_, v_a_962_, v_x_963_);
lean_dec(v_x_963_);
lean_dec(v_a_962_);
return v_res_964_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(13u);
v___x_980_ = lean_nat_to_int(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_unsigned_to_nat(15u);
v___x_985_ = lean_nat_to_int(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_unsigned_to_nat(16u);
v___x_990_ = lean_nat_to_int(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(lean_object* v_x_991_){
_start:
{
lean_object* v_numFields_992_; lean_object* v_numOverlaps_993_; uint8_t v_hasUnitThunk_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_numFields_992_ = lean_ctor_get(v_x_991_, 0);
lean_inc(v_numFields_992_);
v_numOverlaps_993_ = lean_ctor_get(v_x_991_, 1);
lean_inc(v_numOverlaps_993_);
v_hasUnitThunk_994_ = lean_ctor_get_uint8(v_x_991_, sizeof(void*)*2);
lean_dec_ref(v_x_991_);
v___x_995_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_996_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3));
v___x_997_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_998_ = l_Nat_reprFast(v_numFields_992_);
v___x_999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
v___x_1000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_997_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = 0;
v___x_1002_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_996_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_box(1);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6));
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_995_);
v___x_1011_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7);
v___x_1012_ = l_Nat_reprFast(v_numOverlaps_993_);
v___x_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*1, v___x_1001_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1010_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1004_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v___x_1006_);
v___x_1019_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9));
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_995_);
v___x_1022_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10);
v___x_1023_ = l_Bool_repr___redArg(v_hasUnitThunk_994_);
v___x_1024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set_uint8(v___x_1025_, sizeof(void*)*1, v___x_1001_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1021_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1028_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1026_);
v___x_1030_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1027_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*1, v___x_1001_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr(lean_object* v_x_1034_, lean_object* v_prec_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_x_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(lean_object* v_x_1037_, lean_object* v_prec_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_Match_instReprAltParamInfo_repr(v_x_1037_, v_prec_1038_);
lean_dec(v_prec_1038_);
return v_res_1039_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_numFields_1044_; lean_object* v_numOverlaps_1045_; uint8_t v_hasUnitThunk_1046_; lean_object* v_numFields_1047_; lean_object* v_numOverlaps_1048_; uint8_t v_hasUnitThunk_1049_; uint8_t v___x_1050_; 
v_numFields_1044_ = lean_ctor_get(v_x_1042_, 0);
v_numOverlaps_1045_ = lean_ctor_get(v_x_1042_, 1);
v_hasUnitThunk_1046_ = lean_ctor_get_uint8(v_x_1042_, sizeof(void*)*2);
v_numFields_1047_ = lean_ctor_get(v_x_1043_, 0);
v_numOverlaps_1048_ = lean_ctor_get(v_x_1043_, 1);
v_hasUnitThunk_1049_ = lean_ctor_get_uint8(v_x_1043_, sizeof(void*)*2);
v___x_1050_ = lean_nat_dec_eq(v_numFields_1044_, v_numFields_1047_);
if (v___x_1050_ == 0)
{
return v___x_1050_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_nat_dec_eq(v_numOverlaps_1045_, v_numOverlaps_1048_);
if (v___x_1051_ == 0)
{
return v___x_1051_;
}
else
{
if (v_hasUnitThunk_1049_ == 0)
{
if (v_hasUnitThunk_1046_ == 0)
{
return v___x_1051_;
}
else
{
return v_hasUnitThunk_1049_;
}
}
else
{
return v_hasUnitThunk_1046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed(lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v_x_1052_, v_x_1053_);
lean_dec_ref(v_x_1053_);
lean_dec_ref(v_x_1052_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1060_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
v___x_1061_ = lean_box(0);
v___x_1062_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0));
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
lean_ctor_set(v___x_1064_, 2, v___x_1062_);
lean_ctor_set(v___x_1064_, 3, v___x_1061_);
lean_ctor_set(v___x_1064_, 4, v___x_1062_);
lean_ctor_set(v___x_1064_, 5, v___x_1060_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo(void){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1));
return v___x_1069_;
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1081_; 
v_val_1070_ = lean_ctor_get(v_x_1067_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1067_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1072_ = v_x_1067_;
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_val_1070_);
lean_dec(v_x_1067_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3));
v___x_1075_ = l_Nat_reprFast(v_val_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 3);
lean_ctor_set(v___x_1072_, 0, v___x_1075_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1074_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Repr_addAppParen(v___x_1078_, v_x_1068_);
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_x_1082_, v_x_1083_);
lean_dec(v_x_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
if (lean_obj_tag(v_x_1087_) == 0)
{
lean_dec(v_x_1085_);
return v_x_1086_;
}
else
{
lean_object* v_head_1088_; lean_object* v_tail_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1099_; 
v_head_1088_ = lean_ctor_get(v_x_1087_, 0);
v_tail_1089_ = lean_ctor_get(v_x_1087_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1087_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1091_ = v_x_1087_;
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_tail_1089_);
lean_inc(v_head_1088_);
lean_dec(v_x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
lean_inc(v_x_1085_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 5);
lean_ctor_set(v___x_1091_, 1, v_x_1085_);
lean_ctor_set(v___x_1091_, 0, v_x_1086_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_x_1086_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_x_1085_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1088_);
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v_x_1086_ = v___x_1096_;
v_x_1087_ = v_tail_1089_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_dec(v_x_1100_);
return v_x_1101_;
}
else
{
lean_object* v_head_1103_; lean_object* v_tail_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v_head_1103_ = lean_ctor_get(v_x_1102_, 0);
v_tail_1104_ = lean_ctor_get(v_x_1102_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v_x_1102_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_tail_1104_);
lean_inc(v_head_1103_);
lean_dec(v_x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
lean_inc(v_x_1100_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 5);
lean_ctor_set(v___x_1106_, 1, v_x_1100_);
lean_ctor_set(v___x_1106_, 0, v_x_1101_);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_x_1101_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_x_1100_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1103_);
v___x_1111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_1100_, v___x_1111_, v_tail_1104_);
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
if (lean_obj_tag(v_x_1115_) == 0)
{
lean_object* v___x_1117_; 
lean_dec(v_x_1116_);
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
else
{
lean_object* v_tail_1118_; 
v_tail_1118_ = lean_ctor_get(v_x_1115_, 1);
if (lean_obj_tag(v_tail_1118_) == 0)
{
lean_object* v_head_1119_; lean_object* v___x_1120_; 
lean_dec(v_x_1116_);
v_head_1119_ = lean_ctor_get(v_x_1115_, 0);
lean_inc(v_head_1119_);
lean_dec_ref_known(v_x_1115_, 2);
v___x_1120_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1119_);
return v___x_1120_;
}
else
{
lean_object* v_head_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_inc(v_tail_1118_);
v_head_1121_ = lean_ctor_get(v_x_1115_, 0);
lean_inc(v_head_1121_);
lean_dec_ref_known(v_x_1115_, 2);
v___x_1122_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1121_);
v___x_1123_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(v_x_1116_, v___x_1122_, v_tail_1118_);
return v___x_1123_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0));
v___x_1126_ = lean_string_length(v___x_1125_);
return v___x_1126_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1);
v___x_1128_ = lean_nat_to_int(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(lean_object* v_xs_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = lean_array_get_size(v_xs_1134_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_nat_dec_eq(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1138_ = lean_array_to_list(v_xs_1134_);
v___x_1139_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_1140_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(v___x_1138_, v___x_1139_);
v___x_1141_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1142_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v___x_1140_);
v___x_1144_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_1145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1141_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Std_Format_fill(v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
lean_dec_ref(v_xs_1134_);
v___x_1148_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1151_) == 0)
{
lean_dec(v_x_1149_);
return v_x_1150_;
}
else
{
lean_object* v_head_1152_; lean_object* v_tail_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1163_; 
v_head_1152_ = lean_ctor_get(v_x_1151_, 0);
v_tail_1153_ = lean_ctor_get(v_x_1151_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_x_1151_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1155_ = v_x_1151_;
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_tail_1153_);
lean_inc(v_head_1152_);
lean_dec(v_x_1151_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
lean_inc(v_x_1149_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 5);
lean_ctor_set(v___x_1155_, 1, v_x_1149_);
lean_ctor_set(v___x_1155_, 0, v_x_1150_);
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_x_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_x_1149_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1152_);
v___x_1160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v_x_1150_ = v___x_1160_;
v_x_1151_ = v_tail_1153_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
if (lean_obj_tag(v_x_1166_) == 0)
{
lean_dec(v_x_1164_);
return v_x_1165_;
}
else
{
lean_object* v_head_1167_; lean_object* v_tail_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1178_; 
v_head_1167_ = lean_ctor_get(v_x_1166_, 0);
v_tail_1168_ = lean_ctor_get(v_x_1166_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_x_1166_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1170_ = v_x_1166_;
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_tail_1168_);
lean_inc(v_head_1167_);
lean_dec(v_x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
lean_inc(v_x_1164_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 5);
lean_ctor_set(v___x_1170_, 1, v_x_1164_);
lean_ctor_set(v___x_1170_, 0, v_x_1165_);
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_x_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_x_1164_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1167_);
v___x_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(v_x_1164_, v___x_1175_, v_tail_1168_);
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
lean_object* v___x_1181_; 
lean_dec(v_x_1180_);
v___x_1181_ = lean_box(0);
return v___x_1181_;
}
else
{
lean_object* v_tail_1182_; 
v_tail_1182_ = lean_ctor_get(v_x_1179_, 1);
if (lean_obj_tag(v_tail_1182_) == 0)
{
lean_object* v_head_1183_; lean_object* v___x_1184_; 
lean_dec(v_x_1180_);
v_head_1183_ = lean_ctor_get(v_x_1179_, 0);
lean_inc(v_head_1183_);
lean_dec_ref_known(v_x_1179_, 2);
v___x_1184_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1183_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_inc(v_tail_1182_);
v_head_1185_ = lean_ctor_get(v_x_1179_, 0);
lean_inc(v_head_1185_);
lean_dec_ref_known(v_x_1179_, 2);
v___x_1186_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1185_);
v___x_1187_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(v_x_1180_, v___x_1186_, v_tail_1182_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(lean_object* v_xs_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = lean_array_get_size(v_xs_1188_);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_nat_dec_eq(v___x_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1192_ = lean_array_to_list(v_xs_1188_);
v___x_1193_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_1194_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(v___x_1192_, v___x_1193_);
v___x_1195_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1196_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1194_);
v___x_1198_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_1199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1195_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = l_Std_Format_fill(v___x_1200_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; 
lean_dec_ref(v_xs_1188_);
v___x_1202_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1202_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(12u);
v___x_1219_ = lean_nat_to_int(v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_unsigned_to_nat(14u);
v___x_1227_ = lean_nat_to_int(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object* v_x_1231_){
_start:
{
lean_object* v_numParams_1232_; lean_object* v_numDiscrs_1233_; lean_object* v_altInfos_1234_; lean_object* v_uElimPos_x3f_1235_; lean_object* v_discrInfos_1236_; lean_object* v_overlaps_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_numParams_1232_ = lean_ctor_get(v_x_1231_, 0);
lean_inc(v_numParams_1232_);
v_numDiscrs_1233_ = lean_ctor_get(v_x_1231_, 1);
lean_inc(v_numDiscrs_1233_);
v_altInfos_1234_ = lean_ctor_get(v_x_1231_, 2);
lean_inc_ref(v_altInfos_1234_);
v_uElimPos_x3f_1235_ = lean_ctor_get(v_x_1231_, 3);
lean_inc(v_uElimPos_x3f_1235_);
v_discrInfos_1236_ = lean_ctor_get(v_x_1231_, 4);
lean_inc_ref(v_discrInfos_1236_);
v_overlaps_1237_ = lean_ctor_get(v_x_1231_, 5);
lean_inc_ref(v_overlaps_1237_);
lean_dec_ref(v_x_1231_);
v___x_1238_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3));
v___x_1240_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_1241_ = l_Nat_reprFast(v_numParams_1232_);
v___x_1242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1240_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = 0;
v___x_1245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*1, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1239_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_box(1);
v___x_1250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5));
v___x_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1238_);
v___x_1254_ = l_Nat_reprFast(v_numDiscrs_1233_);
v___x_1255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1240_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*1, v___x_1244_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1253_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1247_);
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1249_);
v___x_1261_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7));
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1238_);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8);
v___x_1265_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(v_altInfos_1234_);
v___x_1266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set_uint8(v___x_1267_, sizeof(void*)*1, v___x_1244_);
v___x_1268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1263_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1247_);
v___x_1270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___x_1249_);
v___x_1271_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10));
v___x_1272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1238_);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_uElimPos_x3f_1235_, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1240_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*1, v___x_1244_);
v___x_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1273_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v___x_1247_);
v___x_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v___x_1249_);
v___x_1281_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12));
v___x_1282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1238_);
v___x_1284_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13);
v___x_1285_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(v_discrInfos_1236_);
v___x_1286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*1, v___x_1244_);
v___x_1288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1283_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v___x_1247_);
v___x_1290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1249_);
v___x_1291_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15));
v___x_1292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1238_);
v___x_1294_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_overlaps_1237_);
v___x_1295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1264_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set_uint8(v___x_1296_, sizeof(void*)*1, v___x_1244_);
v___x_1297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1293_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1299_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1297_);
v___x_1301_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1298_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*1, v___x_1244_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr(lean_object* v_x_1305_, lean_object* v_prec_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_x_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(lean_object* v_x_1308_, lean_object* v_prec_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_Match_instReprMatcherInfo_repr(v_x_1308_, v_prec_1309_);
lean_dec(v_prec_1309_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object* v_info_1313_){
_start:
{
lean_object* v_altInfos_1314_; lean_object* v___x_1315_; 
v_altInfos_1314_ = lean_ctor_get(v_info_1313_, 2);
v___x_1315_ = lean_array_get_size(v_altInfos_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(lean_object* v_info_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1316_);
lean_dec_ref(v_info_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object* v_info_1318_){
_start:
{
lean_object* v_numParams_1319_; lean_object* v_numDiscrs_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_numParams_1319_ = lean_ctor_get(v_info_1318_, 0);
v_numDiscrs_1320_ = lean_ctor_get(v_info_1318_, 1);
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_add(v_numParams_1319_, v___x_1321_);
v___x_1323_ = lean_nat_add(v___x_1322_, v_numDiscrs_1320_);
lean_dec(v___x_1322_);
v___x_1324_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1318_);
v___x_1325_ = lean_nat_add(v___x_1323_, v___x_1324_);
lean_dec(v___x_1324_);
lean_dec(v___x_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity___boxed(lean_object* v_info_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Meta_Match_MatcherInfo_arity(v_info_1326_);
lean_dec_ref(v_info_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object* v_info_1328_){
_start:
{
lean_object* v_numParams_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_numParams_1329_ = lean_ctor_get(v_info_1328_, 0);
v___x_1330_ = lean_unsigned_to_nat(1u);
v___x_1331_ = lean_nat_add(v_numParams_1329_, v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(lean_object* v_info_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1332_);
lean_dec_ref(v_info_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange(lean_object* v_info_1334_){
_start:
{
lean_object* v_numDiscrs_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_numDiscrs_1335_ = lean_ctor_get(v_info_1334_, 1);
v___x_1336_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1334_);
v___x_1337_ = lean_nat_add(v___x_1336_, v_numDiscrs_1335_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(lean_object* v_info_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(v_info_1339_);
lean_dec_ref(v_info_1339_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object* v_info_1341_){
_start:
{
lean_object* v_numParams_1342_; lean_object* v_numDiscrs_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_numParams_1342_ = lean_ctor_get(v_info_1341_, 0);
v_numDiscrs_1343_ = lean_ctor_get(v_info_1341_, 1);
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_add(v_numParams_1342_, v___x_1344_);
v___x_1346_ = lean_nat_add(v___x_1345_, v_numDiscrs_1343_);
lean_dec(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(lean_object* v_info_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1347_);
lean_dec_ref(v_info_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange(lean_object* v_info_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1350_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1349_);
v___x_1351_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1349_);
v___x_1352_ = lean_nat_add(v___x_1350_, v___x_1351_);
lean_dec(v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1350_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(lean_object* v_info_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_Match_MatcherInfo_getAltRange(v_info_1354_);
lean_dec_ref(v_info_1354_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object* v_info_1356_){
_start:
{
lean_object* v_numParams_1357_; 
v_numParams_1357_ = lean_ctor_get(v_info_1356_, 0);
lean_inc(v_numParams_1357_);
return v_numParams_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(lean_object* v_info_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_info_1358_);
lean_dec_ref(v_info_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(lean_object* v_as_1360_, size_t v_sz_1361_, size_t v_i_1362_, lean_object* v_b_1363_){
_start:
{
lean_object* v_a_1365_; uint8_t v___x_1369_; 
v___x_1369_ = lean_usize_dec_lt(v_i_1362_, v_sz_1361_);
if (v___x_1369_ == 0)
{
return v_b_1363_;
}
else
{
lean_object* v_a_1370_; 
v_a_1370_ = lean_array_uget_borrowed(v_as_1360_, v_i_1362_);
if (lean_obj_tag(v_a_1370_) == 0)
{
v_a_1365_ = v_b_1363_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_b_1363_, v___x_1371_);
lean_dec(v_b_1363_);
v_a_1365_ = v___x_1372_;
goto v___jp_1364_;
}
}
v___jp_1364_:
{
size_t v___x_1366_; size_t v___x_1367_; 
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1362_, v___x_1366_);
v_i_1362_ = v___x_1367_;
v_b_1363_ = v_a_1365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0___boxed(lean_object* v_as_1373_, lean_object* v_sz_1374_, lean_object* v_i_1375_, lean_object* v_b_1376_){
_start:
{
size_t v_sz_boxed_1377_; size_t v_i_boxed_1378_; lean_object* v_res_1379_; 
v_sz_boxed_1377_ = lean_unbox_usize(v_sz_1374_);
lean_dec(v_sz_1374_);
v_i_boxed_1378_ = lean_unbox_usize(v_i_1375_);
lean_dec(v_i_1375_);
v_res_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_as_1373_, v_sz_boxed_1377_, v_i_boxed_1378_, v_b_1376_);
lean_dec_ref(v_as_1373_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos(lean_object* v_infos_1380_){
_start:
{
lean_object* v_r_1381_; size_t v_sz_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v_r_1381_ = lean_unsigned_to_nat(0u);
v_sz_1382_ = lean_array_size(v_infos_1380_);
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_infos_1380_, v_sz_1382_, v___x_1383_, v_r_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(lean_object* v_infos_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_infos_1385_);
lean_dec_ref(v_infos_1385_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object* v_info_1387_){
_start:
{
lean_object* v_discrInfos_1388_; lean_object* v___x_1389_; 
v_discrInfos_1388_ = lean_ctor_get(v_info_1387_, 4);
v___x_1389_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(lean_object* v_info_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1390_);
lean_dec_ref(v_info_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(lean_object* v_info_1392_, size_t v_sz_1393_, size_t v_i_1394_, lean_object* v_bs_1395_){
_start:
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_usize_dec_lt(v_i_1394_, v_sz_1393_);
if (v___x_1396_ == 0)
{
return v_bs_1395_;
}
else
{
lean_object* v_v_1397_; lean_object* v_numFields_1398_; lean_object* v_numOverlaps_1399_; uint8_t v_hasUnitThunk_1400_; lean_object* v___x_1401_; lean_object* v_bs_x27_1402_; lean_object* v___x_1403_; lean_object* v___y_1405_; 
v_v_1397_ = lean_array_uget_borrowed(v_bs_1395_, v_i_1394_);
v_numFields_1398_ = lean_ctor_get(v_v_1397_, 0);
lean_inc(v_numFields_1398_);
v_numOverlaps_1399_ = lean_ctor_get(v_v_1397_, 1);
lean_inc(v_numOverlaps_1399_);
v_hasUnitThunk_1400_ = lean_ctor_get_uint8(v_v_1397_, sizeof(void*)*2);
v___x_1401_ = lean_unsigned_to_nat(0u);
v_bs_x27_1402_ = lean_array_uset(v_bs_1395_, v_i_1394_, v___x_1401_);
v___x_1403_ = lean_nat_add(v_numFields_1398_, v_numOverlaps_1399_);
lean_dec(v_numOverlaps_1399_);
lean_dec(v_numFields_1398_);
if (v_hasUnitThunk_1400_ == 0)
{
v___y_1405_ = v___x_1401_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_unsigned_to_nat(1u);
v___y_1405_ = v___x_1413_;
goto v___jp_1404_;
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1406_ = lean_nat_add(v___x_1403_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec(v___x_1403_);
v___x_1407_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1392_);
v___x_1408_ = lean_nat_add(v___x_1406_, v___x_1407_);
lean_dec(v___x_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = ((size_t)1ULL);
v___x_1410_ = lean_usize_add(v_i_1394_, v___x_1409_);
v___x_1411_ = lean_array_uset(v_bs_x27_1402_, v_i_1394_, v___x_1408_);
v_i_1394_ = v___x_1410_;
v_bs_1395_ = v___x_1411_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0___boxed(lean_object* v_info_1414_, lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_bs_1417_){
_start:
{
size_t v_sz_boxed_1418_; size_t v_i_boxed_1419_; lean_object* v_res_1420_; 
v_sz_boxed_1418_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1419_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1414_, v_sz_boxed_1418_, v_i_boxed_1419_, v_bs_1417_);
lean_dec_ref(v_info_1414_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object* v_info_1421_){
_start:
{
lean_object* v_altInfos_1422_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v_altInfos_1422_ = lean_ctor_get(v_info_1421_, 2);
lean_inc_ref(v_altInfos_1422_);
v_sz_1423_ = lean_array_size(v_altInfos_1422_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1421_, v_sz_1423_, v___x_1424_, v_altInfos_1422_);
lean_dec_ref(v_info_1421_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_unsigned_to_nat(16u);
v___x_1428_ = lean_mk_array(v___x_1427_, v___x_1426_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__0, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__2, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__3, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3);
v___x_1436_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__1, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1);
v___x_1437_ = 1;
v___x_1438_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1435_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*2, v___x_1437_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState(void){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__4, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4);
return v___x_1439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_1440_, lean_object* v_x_1441_){
_start:
{
if (lean_obj_tag(v_x_1441_) == 0)
{
uint8_t v___x_1442_; 
v___x_1442_ = 0;
return v___x_1442_;
}
else
{
lean_object* v_key_1443_; lean_object* v_tail_1444_; uint8_t v___x_1445_; 
v_key_1443_ = lean_ctor_get(v_x_1441_, 0);
v_tail_1444_ = lean_ctor_get(v_x_1441_, 2);
v___x_1445_ = lean_name_eq(v_key_1443_, v_a_1440_);
if (v___x_1445_ == 0)
{
v_x_1441_ = v_tail_1444_;
goto _start;
}
else
{
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_1447_, lean_object* v_x_1448_){
_start:
{
uint8_t v_res_1449_; lean_object* v_r_1450_; 
v_res_1449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1447_, v_x_1448_);
lean_dec(v_x_1448_);
lean_dec(v_a_1447_);
v_r_1450_ = lean_box(v_res_1449_);
return v_r_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
if (lean_obj_tag(v_x_1452_) == 0)
{
return v_x_1451_;
}
else
{
lean_object* v_key_1453_; lean_object* v_value_1454_; lean_object* v_tail_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1481_; 
v_key_1453_ = lean_ctor_get(v_x_1452_, 0);
v_value_1454_ = lean_ctor_get(v_x_1452_, 1);
v_tail_1455_ = lean_ctor_get(v_x_1452_, 2);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1457_ = v_x_1452_;
v_isShared_1458_ = v_isSharedCheck_1481_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_tail_1455_);
lean_inc(v_value_1454_);
lean_inc(v_key_1453_);
lean_dec(v_x_1452_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1481_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; uint64_t v___y_1461_; 
v___x_1459_ = lean_array_get_size(v_x_1451_);
if (lean_obj_tag(v_key_1453_) == 0)
{
uint64_t v___x_1479_; 
v___x_1479_ = 1723ULL;
v___y_1461_ = v___x_1479_;
goto v___jp_1460_;
}
else
{
uint64_t v_hash_1480_; 
v_hash_1480_ = lean_ctor_get_uint64(v_key_1453_, sizeof(void*)*2);
v___y_1461_ = v_hash_1480_;
goto v___jp_1460_;
}
v___jp_1460_:
{
uint64_t v___x_1462_; uint64_t v___x_1463_; uint64_t v_fold_1464_; uint64_t v___x_1465_; uint64_t v___x_1466_; uint64_t v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1462_ = 32ULL;
v___x_1463_ = lean_uint64_shift_right(v___y_1461_, v___x_1462_);
v_fold_1464_ = lean_uint64_xor(v___y_1461_, v___x_1463_);
v___x_1465_ = 16ULL;
v___x_1466_ = lean_uint64_shift_right(v_fold_1464_, v___x_1465_);
v___x_1467_ = lean_uint64_xor(v_fold_1464_, v___x_1466_);
v___x_1468_ = lean_uint64_to_usize(v___x_1467_);
v___x_1469_ = lean_usize_of_nat(v___x_1459_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = lean_usize_sub(v___x_1469_, v___x_1470_);
v___x_1472_ = lean_usize_land(v___x_1468_, v___x_1471_);
v___x_1473_ = lean_array_uget_borrowed(v_x_1451_, v___x_1472_);
lean_inc(v___x_1473_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 2, v___x_1473_);
v___x_1475_ = v___x_1457_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_key_1453_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_value_1454_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_array_uset(v_x_1451_, v___x_1472_, v___x_1475_);
v_x_1451_ = v___x_1476_;
v_x_1452_ = v_tail_1455_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_1482_, lean_object* v_source_1483_, lean_object* v_target_1484_){
_start:
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = lean_array_get_size(v_source_1483_);
v___x_1486_ = lean_nat_dec_lt(v_i_1482_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec_ref(v_source_1483_);
lean_dec(v_i_1482_);
return v_target_1484_;
}
else
{
lean_object* v_es_1487_; lean_object* v___x_1488_; lean_object* v_source_1489_; lean_object* v_target_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_es_1487_ = lean_array_fget(v_source_1483_, v_i_1482_);
v___x_1488_ = lean_box(0);
v_source_1489_ = lean_array_fset(v_source_1483_, v_i_1482_, v___x_1488_);
v_target_1490_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_1484_, v_es_1487_);
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = lean_nat_add(v_i_1482_, v___x_1491_);
lean_dec(v_i_1482_);
v_i_1482_ = v___x_1492_;
v_source_1483_ = v_source_1489_;
v_target_1484_ = v_target_1490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_data_1494_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_nbuckets_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1495_ = lean_array_get_size(v_data_1494_);
v___x_1496_ = lean_unsigned_to_nat(2u);
v_nbuckets_1497_ = lean_nat_mul(v___x_1495_, v___x_1496_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_mk_array(v_nbuckets_1497_, v___x_1499_);
v___x_1501_ = lean_array_propagate_mark(v_data_1494_, v___x_1500_);
v___x_1502_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_1498_, v_data_1494_, v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_a_1503_, lean_object* v_b_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_dec(v_b_1504_);
lean_dec(v_a_1503_);
return v_x_1505_;
}
else
{
lean_object* v_key_1506_; lean_object* v_value_1507_; lean_object* v_tail_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1520_; 
v_key_1506_ = lean_ctor_get(v_x_1505_, 0);
v_value_1507_ = lean_ctor_get(v_x_1505_, 1);
v_tail_1508_ = lean_ctor_get(v_x_1505_, 2);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_x_1505_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1510_ = v_x_1505_;
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_tail_1508_);
lean_inc(v_value_1507_);
lean_inc(v_key_1506_);
lean_dec(v_x_1505_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_name_eq(v_key_1506_, v_a_1503_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1503_, v_b_1504_, v_tail_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 2, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_key_1506_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_value_1507_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
lean_object* v___x_1518_; 
lean_dec(v_value_1507_);
lean_dec(v_key_1506_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v_b_1504_);
lean_ctor_set(v___x_1510_, 0, v_a_1503_);
v___x_1518_ = v___x_1510_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_b_1504_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_tail_1508_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(lean_object* v_m_1521_, lean_object* v_a_1522_, lean_object* v_b_1523_){
_start:
{
lean_object* v_size_1524_; lean_object* v_buckets_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1571_; 
v_size_1524_ = lean_ctor_get(v_m_1521_, 0);
v_buckets_1525_ = lean_ctor_get(v_m_1521_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_m_1521_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1527_ = v_m_1521_;
v_isShared_1528_ = v_isSharedCheck_1571_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_buckets_1525_);
lean_inc(v_size_1524_);
lean_dec(v_m_1521_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1571_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; uint64_t v___y_1531_; 
v___x_1529_ = lean_array_get_size(v_buckets_1525_);
if (lean_obj_tag(v_a_1522_) == 0)
{
uint64_t v___x_1569_; 
v___x_1569_ = 1723ULL;
v___y_1531_ = v___x_1569_;
goto v___jp_1530_;
}
else
{
uint64_t v_hash_1570_; 
v_hash_1570_ = lean_ctor_get_uint64(v_a_1522_, sizeof(void*)*2);
v___y_1531_ = v_hash_1570_;
goto v___jp_1530_;
}
v___jp_1530_:
{
uint64_t v___x_1532_; uint64_t v___x_1533_; uint64_t v_fold_1534_; uint64_t v___x_1535_; uint64_t v___x_1536_; uint64_t v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; lean_object* v_bkt_1543_; uint8_t v___x_1544_; 
v___x_1532_ = 32ULL;
v___x_1533_ = lean_uint64_shift_right(v___y_1531_, v___x_1532_);
v_fold_1534_ = lean_uint64_xor(v___y_1531_, v___x_1533_);
v___x_1535_ = 16ULL;
v___x_1536_ = lean_uint64_shift_right(v_fold_1534_, v___x_1535_);
v___x_1537_ = lean_uint64_xor(v_fold_1534_, v___x_1536_);
v___x_1538_ = lean_uint64_to_usize(v___x_1537_);
v___x_1539_ = lean_usize_of_nat(v___x_1529_);
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_sub(v___x_1539_, v___x_1540_);
v___x_1542_ = lean_usize_land(v___x_1538_, v___x_1541_);
v_bkt_1543_ = lean_array_uget_borrowed(v_buckets_1525_, v___x_1542_);
v___x_1544_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1522_, v_bkt_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v_size_x27_1546_; lean_object* v___x_1547_; lean_object* v_buckets_x27_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1545_ = lean_unsigned_to_nat(1u);
v_size_x27_1546_ = lean_nat_add(v_size_1524_, v___x_1545_);
lean_dec(v_size_1524_);
lean_inc(v_bkt_1543_);
v___x_1547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1522_);
lean_ctor_set(v___x_1547_, 1, v_b_1523_);
lean_ctor_set(v___x_1547_, 2, v_bkt_1543_);
v_buckets_x27_1548_ = lean_array_uset(v_buckets_1525_, v___x_1542_, v___x_1547_);
v___x_1549_ = lean_unsigned_to_nat(4u);
v___x_1550_ = lean_nat_mul(v_size_x27_1546_, v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(3u);
v___x_1552_ = lean_nat_div(v___x_1550_, v___x_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_array_get_size(v_buckets_x27_1548_);
v___x_1554_ = lean_nat_dec_le(v___x_1552_, v___x_1553_);
lean_dec(v___x_1552_);
if (v___x_1554_ == 0)
{
lean_object* v_val_1555_; lean_object* v___x_1557_; 
v_val_1555_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_1548_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_val_1555_);
lean_ctor_set(v___x_1527_, 0, v_size_x27_1546_);
v___x_1557_ = v___x_1527_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_size_x27_1546_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_val_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
else
{
lean_object* v___x_1560_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v_buckets_x27_1548_);
lean_ctor_set(v___x_1527_, 0, v_size_x27_1546_);
v___x_1560_ = v___x_1527_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_size_x27_1546_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_buckets_x27_1548_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v___x_1562_; lean_object* v_buckets_x27_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_inc(v_bkt_1543_);
v___x_1562_ = lean_box(0);
v_buckets_x27_1563_ = lean_array_uset(v_buckets_1525_, v___x_1542_, v___x_1562_);
v___x_1564_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1522_, v_b_1523_, v_bkt_1543_);
v___x_1565_ = lean_array_uset(v_buckets_x27_1563_, v___x_1542_, v___x_1564_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1565_);
v___x_1567_ = v___x_1527_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_size_1524_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_){
_start:
{
lean_object* v_ks_1576_; lean_object* v_vs_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1601_; 
v_ks_1576_ = lean_ctor_get(v_x_1572_, 0);
v_vs_1577_ = lean_ctor_get(v_x_1572_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1579_ = v_x_1572_;
v_isShared_1580_ = v_isSharedCheck_1601_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_vs_1577_);
lean_inc(v_ks_1576_);
lean_dec(v_x_1572_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1601_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = lean_array_get_size(v_ks_1576_);
v___x_1582_ = lean_nat_dec_lt(v_x_1573_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_dec(v_x_1573_);
v___x_1583_ = lean_array_push(v_ks_1576_, v_x_1574_);
v___x_1584_ = lean_array_push(v_vs_1577_, v_x_1575_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v___x_1584_);
lean_ctor_set(v___x_1579_, 0, v___x_1583_);
v___x_1586_ = v___x_1579_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
lean_object* v_k_x27_1588_; uint8_t v___x_1589_; 
v_k_x27_1588_ = lean_array_fget_borrowed(v_ks_1576_, v_x_1573_);
v___x_1589_ = lean_name_eq(v_x_1574_, v_k_x27_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1591_; 
if (v_isShared_1580_ == 0)
{
v___x_1591_ = v___x_1579_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_ks_1576_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_vs_1577_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_add(v_x_1573_, v___x_1592_);
lean_dec(v_x_1573_);
v_x_1572_ = v___x_1591_;
v_x_1573_ = v___x_1593_;
goto _start;
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1596_ = lean_array_fset(v_ks_1576_, v_x_1573_, v_x_1574_);
v___x_1597_ = lean_array_fset(v_vs_1577_, v_x_1573_, v_x_1575_);
lean_dec(v_x_1573_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v___x_1597_);
lean_ctor_set(v___x_1579_, 0, v___x_1596_);
v___x_1599_ = v___x_1579_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1602_, lean_object* v_k_1603_, lean_object* v_v_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_1602_, v___x_1605_, v_k_1603_, v_v_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1608_, size_t v_x_1609_, size_t v_x_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_object* v_es_1613_; size_t v___x_1614_; size_t v___x_1615_; lean_object* v_j_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_es_1613_ = lean_ctor_get(v_x_1608_, 0);
v___x_1614_ = ((size_t)31ULL);
v___x_1615_ = lean_usize_land(v_x_1609_, v___x_1614_);
v_j_1616_ = lean_usize_to_nat(v___x_1615_);
v___x_1617_ = lean_array_get_size(v_es_1613_);
v___x_1618_ = lean_nat_dec_lt(v_j_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_dec(v_j_1616_);
lean_dec(v_x_1612_);
lean_dec(v_x_1611_);
return v_x_1608_;
}
else
{
lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1657_; 
lean_inc_ref(v_es_1613_);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_x_1608_, 0);
lean_dec(v_unused_1658_);
v___x_1620_ = v_x_1608_;
v_isShared_1621_ = v_isSharedCheck_1657_;
goto v_resetjp_1619_;
}
else
{
lean_dec(v_x_1608_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1657_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_v_1622_; lean_object* v___x_1623_; lean_object* v_xs_x27_1624_; lean_object* v___y_1626_; 
v_v_1622_ = lean_array_fget(v_es_1613_, v_j_1616_);
v___x_1623_ = lean_box(0);
v_xs_x27_1624_ = lean_array_fset(v_es_1613_, v_j_1616_, v___x_1623_);
switch(lean_obj_tag(v_v_1622_))
{
case 0:
{
lean_object* v_key_1631_; lean_object* v_val_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1642_; 
v_key_1631_ = lean_ctor_get(v_v_1622_, 0);
v_val_1632_ = lean_ctor_get(v_v_1622_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_v_1622_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1634_ = v_v_1622_;
v_isShared_1635_ = v_isSharedCheck_1642_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_val_1632_);
lean_inc(v_key_1631_);
lean_dec(v_v_1622_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1642_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_name_eq(v_x_1611_, v_key_1631_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_del_object(v___x_1634_);
v___x_1637_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1631_, v_val_1632_, v_x_1611_, v_x_1612_);
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
v___y_1626_ = v___x_1638_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1640_; 
lean_dec(v_val_1632_);
lean_dec(v_key_1631_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v_x_1612_);
lean_ctor_set(v___x_1634_, 0, v_x_1611_);
v___x_1640_ = v___x_1634_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_x_1611_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_x_1612_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
v___y_1626_ = v___x_1640_;
goto v___jp_1625_;
}
}
}
}
case 1:
{
lean_object* v_node_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1655_; 
v_node_1643_ = lean_ctor_get(v_v_1622_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_v_1622_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1645_ = v_v_1622_;
v_isShared_1646_ = v_isSharedCheck_1655_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_node_1643_);
lean_dec(v_v_1622_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1655_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1647_ = ((size_t)5ULL);
v___x_1648_ = lean_usize_shift_right(v_x_1609_, v___x_1647_);
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_add(v_x_1610_, v___x_1649_);
v___x_1651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_node_1643_, v___x_1648_, v___x_1650_, v_x_1611_, v_x_1612_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1651_);
v___x_1653_ = v___x_1645_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1626_ = v___x_1653_;
goto v___jp_1625_;
}
}
}
default: 
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_x_1611_);
lean_ctor_set(v___x_1656_, 1, v_x_1612_);
v___y_1626_ = v___x_1656_;
goto v___jp_1625_;
}
}
v___jp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_array_fset(v_xs_x27_1624_, v_j_1616_, v___y_1626_);
lean_dec(v_j_1616_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1627_);
v___x_1629_ = v___x_1620_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
else
{
lean_object* v_ks_1659_; lean_object* v_vs_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1678_; 
v_ks_1659_ = lean_ctor_get(v_x_1608_, 0);
v_vs_1660_ = lean_ctor_get(v_x_1608_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1662_ = v_x_1608_;
v_isShared_1663_ = v_isSharedCheck_1678_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_vs_1660_);
lean_inc(v_ks_1659_);
lean_dec(v_x_1608_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1678_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_ks_1659_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_vs_1660_);
v___x_1665_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v_newNode_1666_; size_t v___x_1667_; uint8_t v___x_1668_; 
v_newNode_1666_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1665_, v_x_1611_, v_x_1612_);
v___x_1667_ = ((size_t)7ULL);
v___x_1668_ = lean_usize_dec_le(v___x_1667_, v_x_1610_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1669_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1666_);
v___x_1670_ = lean_unsigned_to_nat(4u);
v___x_1671_ = lean_nat_dec_lt(v___x_1669_, v___x_1670_);
lean_dec(v___x_1669_);
if (v___x_1671_ == 0)
{
lean_object* v_ks_1672_; lean_object* v_vs_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_ks_1672_ = lean_ctor_get(v_newNode_1666_, 0);
lean_inc_ref(v_ks_1672_);
v_vs_1673_ = lean_ctor_get(v_newNode_1666_, 1);
lean_inc_ref(v_vs_1673_);
lean_dec_ref(v_newNode_1666_);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1610_, v_ks_1672_, v_vs_1673_, v___x_1674_, v___x_1675_);
lean_dec_ref(v_vs_1673_);
lean_dec_ref(v_ks_1672_);
return v___x_1676_;
}
else
{
return v_newNode_1666_;
}
}
else
{
return v_newNode_1666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1679_, lean_object* v_keys_1680_, lean_object* v_vals_1681_, lean_object* v_i_1682_, lean_object* v_entries_1683_){
_start:
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = lean_array_get_size(v_keys_1680_);
v___x_1685_ = lean_nat_dec_lt(v_i_1682_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_dec(v_i_1682_);
return v_entries_1683_;
}
else
{
lean_object* v_k_1686_; lean_object* v_v_1687_; uint64_t v___y_1689_; 
v_k_1686_ = lean_array_fget_borrowed(v_keys_1680_, v_i_1682_);
v_v_1687_ = lean_array_fget_borrowed(v_vals_1681_, v_i_1682_);
if (lean_obj_tag(v_k_1686_) == 0)
{
uint64_t v___x_1700_; 
v___x_1700_ = 1723ULL;
v___y_1689_ = v___x_1700_;
goto v___jp_1688_;
}
else
{
uint64_t v_hash_1701_; 
v_hash_1701_ = lean_ctor_get_uint64(v_k_1686_, sizeof(void*)*2);
v___y_1689_ = v_hash_1701_;
goto v___jp_1688_;
}
v___jp_1688_:
{
size_t v_h_1690_; size_t v___x_1691_; lean_object* v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v_h_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_h_1690_ = lean_uint64_to_usize(v___y_1689_);
v___x_1691_ = ((size_t)5ULL);
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_sub(v_depth_1679_, v___x_1693_);
v___x_1695_ = lean_usize_mul(v___x_1691_, v___x_1694_);
v_h_1696_ = lean_usize_shift_right(v_h_1690_, v___x_1695_);
v___x_1697_ = lean_nat_add(v_i_1682_, v___x_1692_);
lean_dec(v_i_1682_);
lean_inc(v_v_1687_);
lean_inc(v_k_1686_);
v___x_1698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_entries_1683_, v_h_1696_, v_depth_1679_, v_k_1686_, v_v_1687_);
v_i_1682_ = v___x_1697_;
v_entries_1683_ = v___x_1698_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1702_, lean_object* v_keys_1703_, lean_object* v_vals_1704_, lean_object* v_i_1705_, lean_object* v_entries_1706_){
_start:
{
size_t v_depth_boxed_1707_; lean_object* v_res_1708_; 
v_depth_boxed_1707_ = lean_unbox_usize(v_depth_1702_);
lean_dec(v_depth_1702_);
v_res_1708_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1707_, v_keys_1703_, v_vals_1704_, v_i_1705_, v_entries_1706_);
lean_dec_ref(v_vals_1704_);
lean_dec_ref(v_keys_1703_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_){
_start:
{
size_t v_x_1000__boxed_1714_; size_t v_x_1001__boxed_1715_; lean_object* v_res_1716_; 
v_x_1000__boxed_1714_ = lean_unbox_usize(v_x_1710_);
lean_dec(v_x_1710_);
v_x_1001__boxed_1715_ = lean_unbox_usize(v_x_1711_);
lean_dec(v_x_1711_);
v_res_1716_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1709_, v_x_1000__boxed_1714_, v_x_1001__boxed_1715_, v_x_1712_, v_x_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
uint64_t v___y_1721_; 
if (lean_obj_tag(v_x_1718_) == 0)
{
uint64_t v___x_1725_; 
v___x_1725_ = 1723ULL;
v___y_1721_ = v___x_1725_;
goto v___jp_1720_;
}
else
{
uint64_t v_hash_1726_; 
v_hash_1726_ = lean_ctor_get_uint64(v_x_1718_, sizeof(void*)*2);
v___y_1721_ = v_hash_1726_;
goto v___jp_1720_;
}
v___jp_1720_:
{
size_t v___x_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_uint64_to_usize(v___y_1721_);
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1717_, v___x_1722_, v___x_1723_, v_x_1718_, v_x_1719_);
return v___x_1724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(lean_object* v_x_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
uint8_t v_stage_u2081_1730_; 
v_stage_u2081_1730_ = lean_ctor_get_uint8(v_x_1727_, sizeof(void*)*2);
if (v_stage_u2081_1730_ == 0)
{
lean_object* v_map_u2081_1731_; lean_object* v_map_u2082_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1740_; 
v_map_u2081_1731_ = lean_ctor_get(v_x_1727_, 0);
v_map_u2082_1732_ = lean_ctor_get(v_x_1727_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1734_ = v_x_1727_;
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_map_u2082_1732_);
lean_inc(v_map_u2081_1731_);
lean_dec(v_x_1727_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1740_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_map_u2082_1732_, v_x_1728_, v_x_1729_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_map_u2081_1731_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1739_, sizeof(void*)*2, v_stage_u2081_1730_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_map_u2081_1741_; lean_object* v_map_u2082_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1750_; 
v_map_u2081_1741_ = lean_ctor_get(v_x_1727_, 0);
v_map_u2082_1742_ = lean_ctor_get(v_x_1727_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_x_1727_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1744_ = v_x_1727_;
v_isShared_1745_ = v_isSharedCheck_1750_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_map_u2082_1742_);
lean_inc(v_map_u2081_1741_);
lean_dec(v_x_1727_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1750_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_map_u2081_1741_, v_x_1728_, v_x_1729_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1746_);
v___x_1748_ = v___x_1744_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_map_u2082_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*2, v_stage_u2081_1730_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_addEntry(lean_object* v_s_1751_, lean_object* v_e_1752_){
_start:
{
lean_object* v_name_1753_; lean_object* v_info_1754_; lean_object* v___x_1755_; 
v_name_1753_ = lean_ctor_get(v_e_1752_, 0);
lean_inc(v_name_1753_);
v_info_1754_ = lean_ctor_get(v_e_1752_, 1);
lean_inc_ref(v_info_1754_);
lean_dec_ref(v_e_1752_);
v___x_1755_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_s_1751_, v_name_1753_, v_info_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(lean_object* v_00_u03b2_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_x_1757_, v_x_1758_, v_x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_x_1762_, v_x_1763_, v_x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_1766_, lean_object* v_m_1767_, lean_object* v_a_1768_, lean_object* v_b_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_m_1767_, v_a_1768_, v_b_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1771_, lean_object* v_x_1772_, size_t v_x_1773_, size_t v_x_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1772_, v_x_1773_, v_x_1774_, v_x_1775_, v_x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
size_t v_x_1240__boxed_1784_; size_t v_x_1241__boxed_1785_; lean_object* v_res_1786_; 
v_x_1240__boxed_1784_ = lean_unbox_usize(v_x_1780_);
lean_dec(v_x_1780_);
v_x_1241__boxed_1785_ = lean_unbox_usize(v_x_1781_);
lean_dec(v_x_1781_);
v_res_1786_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(v_00_u03b2_1778_, v_x_1779_, v_x_1240__boxed_1784_, v_x_1241__boxed_1785_, v_x_1782_, v_x_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1787_, lean_object* v_a_1788_, lean_object* v_x_1789_){
_start:
{
uint8_t v___x_1790_; 
v___x_1790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1788_, v_x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1791_, lean_object* v_a_1792_, lean_object* v_x_1793_){
_start:
{
uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_res_1794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(v_00_u03b2_1791_, v_a_1792_, v_x_1793_);
lean_dec(v_x_1793_);
lean_dec(v_a_1792_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1796_, lean_object* v_data_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_data_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1799_, lean_object* v_a_1800_, lean_object* v_b_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1800_, v_b_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1804_, lean_object* v_n_1805_, lean_object* v_k_1806_, lean_object* v_v_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1805_, v_k_1806_, v_v_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1809_, size_t v_depth_1810_, lean_object* v_keys_1811_, lean_object* v_vals_1812_, lean_object* v_heq_1813_, lean_object* v_i_1814_, lean_object* v_entries_1815_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1810_, v_keys_1811_, v_vals_1812_, v_i_1814_, v_entries_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1817_, lean_object* v_depth_1818_, lean_object* v_keys_1819_, lean_object* v_vals_1820_, lean_object* v_heq_1821_, lean_object* v_i_1822_, lean_object* v_entries_1823_){
_start:
{
size_t v_depth_boxed_1824_; lean_object* v_res_1825_; 
v_depth_boxed_1824_ = lean_unbox_usize(v_depth_1818_);
lean_dec(v_depth_1818_);
v_res_1825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1817_, v_depth_boxed_1824_, v_keys_1819_, v_vals_1820_, v_heq_1821_, v_i_1822_, v_entries_1823_);
lean_dec_ref(v_vals_1820_);
lean_dec_ref(v_keys_1819_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1826_, lean_object* v_i_1827_, lean_object* v_source_1828_, lean_object* v_target_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_1827_, v_source_1828_, v_target_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1832_, v_x_1833_, v_x_1834_, v_x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_1838_, v_x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(lean_object* v_m_1841_){
_start:
{
uint8_t v_stage_u2081_1842_; 
v_stage_u2081_1842_ = lean_ctor_get_uint8(v_m_1841_, sizeof(void*)*2);
if (v_stage_u2081_1842_ == 0)
{
return v_m_1841_;
}
else
{
lean_object* v_map_u2081_1843_; lean_object* v_map_u2082_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_map_u2081_1843_ = lean_ctor_get(v_m_1841_, 0);
v_map_u2082_1844_ = lean_ctor_get(v_m_1841_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_m_1841_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1846_ = v_m_1841_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_map_u2082_1844_);
lean_inc(v_map_u2081_1843_);
lean_dec(v_m_1841_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = 0;
if (v_isShared_1847_ == 0)
{
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_map_u2081_1843_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_map_u2082_1844_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*2, v___x_1848_);
return v___x_1850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(lean_object* v_00_u03b2_1853_, lean_object* v_m_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_m_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_switch(lean_object* v_s_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_s_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(lean_object* v_env_1858_, lean_object* v_as_1859_, size_t v_i_1860_, size_t v_stop_1861_, lean_object* v_b_1862_){
_start:
{
lean_object* v___y_1864_; uint8_t v___x_1868_; 
v___x_1868_ = lean_usize_dec_eq(v_i_1860_, v_stop_1861_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v_name_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1869_ = lean_array_uget_borrowed(v_as_1859_, v_i_1860_);
v_name_1870_ = lean_ctor_get(v___x_1869_, 0);
v___x_1871_ = 1;
lean_inc_ref(v_env_1858_);
v___x_1872_ = l_Lean_Environment_setExporting(v_env_1858_, v___x_1871_);
lean_inc(v_name_1870_);
v___x_1873_ = l_Lean_Environment_contains(v___x_1872_, v_name_1870_, v___x_1868_);
if (v___x_1873_ == 0)
{
v___y_1864_ = v_b_1862_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1874_; 
lean_inc(v___x_1869_);
v___x_1874_ = lean_array_push(v_b_1862_, v___x_1869_);
v___y_1864_ = v___x_1874_;
goto v___jp_1863_;
}
}
else
{
lean_dec_ref(v_env_1858_);
return v_b_1862_;
}
v___jp_1863_:
{
size_t v___x_1865_; size_t v___x_1866_; 
v___x_1865_ = ((size_t)1ULL);
v___x_1866_ = lean_usize_add(v_i_1860_, v___x_1865_);
v_i_1860_ = v___x_1866_;
v_b_1862_ = v___y_1864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_1875_, lean_object* v_as_1876_, lean_object* v_i_1877_, lean_object* v_stop_1878_, lean_object* v_b_1879_){
_start:
{
size_t v_i_boxed_1880_; size_t v_stop_boxed_1881_; lean_object* v_res_1882_; 
v_i_boxed_1880_ = lean_unbox_usize(v_i_1877_);
lean_dec(v_i_1877_);
v_stop_boxed_1881_ = lean_unbox_usize(v_stop_1878_);
lean_dec(v_stop_1878_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_1875_, v_as_1876_, v_i_boxed_1880_, v_stop_boxed_1881_, v_b_1879_);
lean_dec_ref(v_as_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_env_1885_, lean_object* v_x_1886_, lean_object* v_entries_1887_){
_start:
{
lean_object* v_all_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_all_1888_ = lean_array_mk(v_entries_1887_);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_array_get_size(v_all_1888_);
v___x_1891_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_));
v___x_1892_ = lean_nat_dec_lt(v___x_1889_, v___x_1890_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref(v_env_1885_);
v___x_1893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1891_);
lean_ctor_set(v___x_1893_, 2, v_all_1888_);
return v___x_1893_;
}
else
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_le(v___x_1890_, v___x_1890_);
if (v___x_1894_ == 0)
{
if (v___x_1892_ == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref(v_env_1885_);
v___x_1895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1891_);
lean_ctor_set(v___x_1895_, 1, v___x_1891_);
lean_ctor_set(v___x_1895_, 2, v_all_1888_);
return v___x_1895_;
}
else
{
size_t v___x_1896_; size_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1896_ = ((size_t)0ULL);
v___x_1897_ = lean_usize_of_nat(v___x_1890_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_1885_, v_all_1888_, v___x_1896_, v___x_1897_, v___x_1891_);
lean_inc_ref(v___x_1898_);
v___x_1899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
lean_ctor_set(v___x_1899_, 2, v_all_1888_);
return v___x_1899_;
}
}
else
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = ((size_t)0ULL);
v___x_1901_ = lean_usize_of_nat(v___x_1890_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__0(v_env_1885_, v_all_1888_, v___x_1900_, v___x_1901_, v___x_1891_);
lean_inc_ref(v___x_1902_);
v___x_1903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
lean_ctor_set(v___x_1903_, 2, v_all_1888_);
return v___x_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_env_1904_, lean_object* v_x_1905_, lean_object* v_entries_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_env_1904_, v_x_1905_, v_entries_1906_);
lean_dec_ref(v_x_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_es_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_array_mk(v_es_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_1910_, size_t v_i_1911_, size_t v_stop_1912_, lean_object* v_b_1913_){
_start:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_usize_dec_eq(v_i_1911_, v_stop_1912_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; size_t v___x_1917_; size_t v___x_1918_; 
v___x_1915_ = lean_array_uget_borrowed(v_as_1910_, v_i_1911_);
lean_inc(v___x_1915_);
v___x_1916_ = l_Lean_Meta_Match_Extension_State_addEntry(v_b_1913_, v___x_1915_);
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_add(v_i_1911_, v___x_1917_);
v_i_1911_ = v___x_1918_;
v_b_1913_ = v___x_1916_;
goto _start;
}
else
{
return v_b_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_1920_, lean_object* v_i_1921_, lean_object* v_stop_1922_, lean_object* v_b_1923_){
_start:
{
size_t v_i_boxed_1924_; size_t v_stop_boxed_1925_; lean_object* v_res_1926_; 
v_i_boxed_1924_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_stop_boxed_1925_ = lean_unbox_usize(v_stop_1922_);
lean_dec(v_stop_1922_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v_as_1920_, v_i_boxed_1924_, v_stop_boxed_1925_, v_b_1923_);
lean_dec_ref(v_as_1920_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_1927_, size_t v_i_1928_, size_t v_stop_1929_, lean_object* v_b_1930_){
_start:
{
lean_object* v___y_1932_; uint8_t v___x_1936_; 
v___x_1936_ = lean_usize_dec_eq(v_i_1928_, v_stop_1929_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1937_ = lean_array_uget_borrowed(v_as_1927_, v_i_1928_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = lean_array_get_size(v___x_1937_);
v___x_1940_ = lean_nat_dec_lt(v___x_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
v___y_1932_ = v_b_1930_;
goto v___jp_1931_;
}
else
{
size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = lean_usize_of_nat(v___x_1939_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__1(v___x_1937_, v___x_1941_, v___x_1942_, v_b_1930_);
v___y_1932_ = v___x_1943_;
goto v___jp_1931_;
}
}
else
{
return v_b_1930_;
}
v___jp_1931_:
{
size_t v___x_1933_; size_t v___x_1934_; 
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1928_, v___x_1933_);
v_i_1928_ = v___x_1934_;
v_b_1930_ = v___y_1932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_1944_, lean_object* v_i_1945_, lean_object* v_stop_1946_, lean_object* v_b_1947_){
_start:
{
size_t v_i_boxed_1948_; size_t v_stop_boxed_1949_; lean_object* v_res_1950_; 
v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_stop_boxed_1949_ = lean_unbox_usize(v_stop_1946_);
lean_dec(v_stop_1946_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_1944_, v_i_boxed_1948_, v_stop_boxed_1949_, v_b_1947_);
lean_dec_ref(v_as_1944_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(lean_object* v_initState_1951_, lean_object* v_as_1952_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = lean_array_get_size(v_as_1952_);
v___x_1955_ = lean_nat_dec_lt(v___x_1953_, v___x_1954_);
if (v___x_1955_ == 0)
{
return v_initState_1951_;
}
else
{
size_t v___x_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = ((size_t)0ULL);
v___x_1957_ = lean_usize_of_nat(v___x_1954_);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1_spec__2(v_as_1952_, v___x_1956_, v___x_1957_, v_initState_1951_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_1959_, lean_object* v_as_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v_initState_1959_, v_as_1960_);
lean_dec_ref(v_as_1960_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(lean_object* v_es_1962_){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__4, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4);
v___x_1964_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2__spec__1(v___x_1963_, v_es_1962_);
v___x_1965_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_es_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(v_es_1966_);
lean_dec_ref(v_es_1966_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_));
v___x_1997_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2____boxed(lean_object* v_a_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object* v_env_2000_, lean_object* v_matcherName_2001_, lean_object* v_info_2002_){
_start:
{
lean_object* v___x_2003_; lean_object* v_toEnvExtension_2004_; lean_object* v_asyncMode_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2003_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2004_ = lean_ctor_get(v___x_2003_, 0);
v_asyncMode_2005_ = lean_ctor_get(v_toEnvExtension_2004_, 2);
lean_inc(v_matcherName_2001_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_matcherName_2001_);
lean_ctor_set(v___x_2006_, 1, v_info_2002_);
v___x_2007_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2003_, v_env_2000_, v___x_2006_, v_asyncMode_2005_, v_matcherName_2001_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_2008_, lean_object* v_vals_2009_, lean_object* v_i_2010_, lean_object* v_k_2011_){
_start:
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = lean_array_get_size(v_keys_2008_);
v___x_2013_ = lean_nat_dec_lt(v_i_2010_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_dec(v_i_2010_);
v___x_2014_ = lean_box(0);
return v___x_2014_;
}
else
{
lean_object* v_k_x27_2015_; uint8_t v___x_2016_; 
v_k_x27_2015_ = lean_array_fget_borrowed(v_keys_2008_, v_i_2010_);
v___x_2016_ = lean_name_eq(v_k_2011_, v_k_x27_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_nat_add(v_i_2010_, v___x_2017_);
lean_dec(v_i_2010_);
v_i_2010_ = v___x_2018_;
goto _start;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_array_fget_borrowed(v_vals_2009_, v_i_2010_);
lean_dec(v_i_2010_);
lean_inc(v___x_2020_);
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2022_, lean_object* v_vals_2023_, lean_object* v_i_2024_, lean_object* v_k_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2022_, v_vals_2023_, v_i_2024_, v_k_2025_);
lean_dec(v_k_2025_);
lean_dec_ref(v_vals_2023_);
lean_dec_ref(v_keys_2022_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2027_, size_t v_x_2028_, lean_object* v_x_2029_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
lean_object* v_es_2030_; lean_object* v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; lean_object* v_j_2034_; lean_object* v___x_2035_; 
v_es_2030_ = lean_ctor_get(v_x_2027_, 0);
v___x_2031_ = lean_box(2);
v___x_2032_ = ((size_t)31ULL);
v___x_2033_ = lean_usize_land(v_x_2028_, v___x_2032_);
v_j_2034_ = lean_usize_to_nat(v___x_2033_);
v___x_2035_ = lean_array_get_borrowed(v___x_2031_, v_es_2030_, v_j_2034_);
lean_dec(v_j_2034_);
switch(lean_obj_tag(v___x_2035_))
{
case 0:
{
lean_object* v_key_2036_; lean_object* v_val_2037_; uint8_t v___x_2038_; 
v_key_2036_ = lean_ctor_get(v___x_2035_, 0);
v_val_2037_ = lean_ctor_get(v___x_2035_, 1);
v___x_2038_ = lean_name_eq(v_x_2029_, v_key_2036_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_box(0);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; 
lean_inc(v_val_2037_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_val_2037_);
return v___x_2040_;
}
}
case 1:
{
lean_object* v_node_2041_; size_t v___x_2042_; size_t v___x_2043_; 
v_node_2041_ = lean_ctor_get(v___x_2035_, 0);
v___x_2042_ = ((size_t)5ULL);
v___x_2043_ = lean_usize_shift_right(v_x_2028_, v___x_2042_);
v_x_2027_ = v_node_2041_;
v_x_2028_ = v___x_2043_;
goto _start;
}
default: 
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_box(0);
return v___x_2045_;
}
}
}
else
{
lean_object* v_ks_2046_; lean_object* v_vs_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_ks_2046_ = lean_ctor_get(v_x_2027_, 0);
v_vs_2047_ = lean_ctor_get(v_x_2027_, 1);
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_2046_, v_vs_2047_, v___x_2048_, v_x_2029_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
size_t v_x_533__boxed_2053_; lean_object* v_res_2054_; 
v_x_533__boxed_2053_ = lean_unbox_usize(v_x_2051_);
lean_dec(v_x_2051_);
v_res_2054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2050_, v_x_533__boxed_2053_, v_x_2052_);
lean_dec(v_x_2052_);
lean_dec_ref(v_x_2050_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_2055_, lean_object* v_x_2056_){
_start:
{
uint64_t v___y_2058_; 
if (lean_obj_tag(v_x_2056_) == 0)
{
uint64_t v___x_2061_; 
v___x_2061_ = 1723ULL;
v___y_2058_ = v___x_2061_;
goto v___jp_2057_;
}
else
{
uint64_t v_hash_2062_; 
v_hash_2062_ = lean_ctor_get_uint64(v_x_2056_, sizeof(void*)*2);
v___y_2058_ = v_hash_2062_;
goto v___jp_2057_;
}
v___jp_2057_:
{
size_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_uint64_to_usize(v___y_2058_);
v___x_2060_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2055_, v___x_2059_, v_x_2056_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2063_, v_x_2064_);
lean_dec(v_x_2064_);
lean_dec_ref(v_x_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(lean_object* v_a_2066_, lean_object* v_x_2067_){
_start:
{
if (lean_obj_tag(v_x_2067_) == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_box(0);
return v___x_2068_;
}
else
{
lean_object* v_key_2069_; lean_object* v_value_2070_; lean_object* v_tail_2071_; uint8_t v___x_2072_; 
v_key_2069_ = lean_ctor_get(v_x_2067_, 0);
v_value_2070_ = lean_ctor_get(v_x_2067_, 1);
v_tail_2071_ = lean_ctor_get(v_x_2067_, 2);
v___x_2072_ = lean_name_eq(v_key_2069_, v_a_2066_);
if (v___x_2072_ == 0)
{
v_x_2067_ = v_tail_2071_;
goto _start;
}
else
{
lean_object* v___x_2074_; 
lean_inc(v_value_2070_);
v___x_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_value_2070_);
return v___x_2074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_2075_, lean_object* v_x_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2075_, v_x_2076_);
lean_dec(v_x_2076_);
lean_dec(v_a_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(lean_object* v_m_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_buckets_2080_; lean_object* v___x_2081_; uint64_t v___y_2083_; 
v_buckets_2080_ = lean_ctor_get(v_m_2078_, 1);
v___x_2081_ = lean_array_get_size(v_buckets_2080_);
if (lean_obj_tag(v_a_2079_) == 0)
{
uint64_t v___x_2097_; 
v___x_2097_ = 1723ULL;
v___y_2083_ = v___x_2097_;
goto v___jp_2082_;
}
else
{
uint64_t v_hash_2098_; 
v_hash_2098_ = lean_ctor_get_uint64(v_a_2079_, sizeof(void*)*2);
v___y_2083_ = v_hash_2098_;
goto v___jp_2082_;
}
v___jp_2082_:
{
uint64_t v___x_2084_; uint64_t v___x_2085_; uint64_t v_fold_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; uint64_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2084_ = 32ULL;
v___x_2085_ = lean_uint64_shift_right(v___y_2083_, v___x_2084_);
v_fold_2086_ = lean_uint64_xor(v___y_2083_, v___x_2085_);
v___x_2087_ = 16ULL;
v___x_2088_ = lean_uint64_shift_right(v_fold_2086_, v___x_2087_);
v___x_2089_ = lean_uint64_xor(v_fold_2086_, v___x_2088_);
v___x_2090_ = lean_uint64_to_usize(v___x_2089_);
v___x_2091_ = lean_usize_of_nat(v___x_2081_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_sub(v___x_2091_, v___x_2092_);
v___x_2094_ = lean_usize_land(v___x_2090_, v___x_2093_);
v___x_2095_ = lean_array_uget_borrowed(v_buckets_2080_, v___x_2094_);
v___x_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2079_, v___x_2095_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_m_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_m_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(lean_object* v_x_2102_, lean_object* v_x_2103_){
_start:
{
uint8_t v_stage_u2081_2104_; 
v_stage_u2081_2104_ = lean_ctor_get_uint8(v_x_2102_, sizeof(void*)*2);
if (v_stage_u2081_2104_ == 0)
{
lean_object* v_map_u2081_2105_; lean_object* v_map_u2082_2106_; lean_object* v___x_2107_; 
v_map_u2081_2105_ = lean_ctor_get(v_x_2102_, 0);
v_map_u2082_2106_ = lean_ctor_get(v_x_2102_, 1);
v___x_2107_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_map_u2082_2106_, v_x_2103_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2105_, v_x_2103_);
return v___x_2108_;
}
else
{
return v___x_2107_;
}
}
else
{
lean_object* v_map_u2081_2109_; lean_object* v___x_2110_; 
v_map_u2081_2109_ = lean_ctor_get(v_x_2102_, 0);
v___x_2110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2109_, v_x_2103_);
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_2111_, lean_object* v_x_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2111_, v_x_2112_);
lean_dec(v_x_2112_);
lean_dec_ref(v_x_2111_);
return v_res_2113_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0));
v___x_2116_ = lean_string_utf8_byte_size(v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object* v_env_2117_, lean_object* v_declName_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Name_eraseMacroScopes(v_declName_2118_);
if (lean_obj_tag(v___x_2119_) == 1)
{
lean_object* v_str_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_str_2120_ = lean_ctor_get(v___x_2119_, 1);
lean_inc_ref(v_str_2120_);
lean_dec_ref_known(v___x_2119_, 2);
v___x_2121_ = ((lean_object*)(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0));
v___x_2122_ = lean_string_utf8_byte_size(v_str_2120_);
v___x_2123_ = lean_obj_once(&l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1, &l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1_once, _init_l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__1);
v___x_2124_ = lean_nat_dec_le(v___x_2123_, v___x_2122_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_dec_ref(v_str_2120_);
lean_dec(v_declName_2118_);
lean_dec_ref(v_env_2117_);
v___x_2125_ = lean_box(0);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_string_memcmp(v_str_2120_, v___x_2121_, v___x_2126_, v___x_2126_, v___x_2123_);
lean_dec_ref(v_str_2120_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
lean_dec(v_declName_2118_);
lean_dec_ref(v_env_2117_);
v___x_2128_ = lean_box(0);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v_toEnvExtension_2130_; lean_object* v_asyncMode_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2129_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2130_ = lean_ctor_get(v___x_2129_, 0);
v_asyncMode_2131_ = lean_ctor_get(v_toEnvExtension_2130_, 2);
v___x_2132_ = l_Lean_Meta_Match_Extension_instInhabitedState;
lean_inc(v_declName_2118_);
v___x_2133_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2132_, v___x_2129_, v_env_2117_, v_asyncMode_2131_, v_declName_2118_);
v___x_2134_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v___x_2133_, v_declName_2118_);
lean_dec(v_declName_2118_);
lean_dec(v___x_2133_);
return v___x_2134_;
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec(v___x_2119_);
lean_dec(v_declName_2118_);
lean_dec_ref(v_env_2117_);
v___x_2135_ = lean_box(0);
return v___x_2135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(lean_object* v_00_u03b2_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2137_, v_x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_2140_, lean_object* v_x_2141_, lean_object* v_x_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(v_00_u03b2_2140_, v_x_2141_, v_x_2142_);
lean_dec(v_x_2142_);
lean_dec_ref(v_x_2141_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2145_, v_x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(v_00_u03b2_2148_, v_x_2149_, v_x_2150_);
lean_dec(v_x_2150_);
lean_dec_ref(v_x_2149_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(lean_object* v_00_u03b2_2152_, lean_object* v_m_2153_, lean_object* v_a_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2153_, v_a_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2156_, lean_object* v_m_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(v_00_u03b2_2156_, v_m_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_m_2157_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2160_, lean_object* v_x_2161_, size_t v_x_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2161_, v_x_2162_, v_x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
size_t v_x_727__boxed_2169_; lean_object* v_res_2170_; 
v_x_727__boxed_2169_ = lean_unbox_usize(v_x_2167_);
lean_dec(v_x_2167_);
v_res_2170_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2165_, v_x_2166_, v_x_727__boxed_2169_, v_x_2168_);
lean_dec(v_x_2168_);
lean_dec_ref(v_x_2166_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2171_, lean_object* v_a_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2172_, v_x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2175_, lean_object* v_a_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(v_00_u03b2_2175_, v_a_2176_, v_x_2177_);
lean_dec(v_x_2177_);
lean_dec(v_a_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2179_, lean_object* v_keys_2180_, lean_object* v_vals_2181_, lean_object* v_heq_2182_, lean_object* v_i_2183_, lean_object* v_k_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2180_, v_vals_2181_, v_i_2183_, v_k_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2186_, lean_object* v_keys_2187_, lean_object* v_vals_2188_, lean_object* v_heq_2189_, lean_object* v_i_2190_, lean_object* v_k_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2186_, v_keys_2187_, v_vals_2188_, v_heq_2189_, v_i_2190_, v_k_2191_);
lean_dec(v_k_2191_);
lean_dec_ref(v_vals_2188_);
lean_dec_ref(v_keys_2187_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(lean_object* v_matcherName_2193_, lean_object* v_info_2194_, lean_object* v_env_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2195_, v_matcherName_2193_, v_info_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg(lean_object* v_inst_2197_, lean_object* v_matcherName_2198_, lean_object* v_info_2199_){
_start:
{
lean_object* v_modifyEnv_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; 
v_modifyEnv_2200_ = lean_ctor_get(v_inst_2197_, 1);
lean_inc(v_modifyEnv_2200_);
lean_dec_ref(v_inst_2197_);
v___f_2201_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2201_, 0, v_matcherName_2198_);
lean_closure_set(v___f_2201_, 1, v_info_2199_);
v___x_2202_ = lean_apply_1(v_modifyEnv_2200_, v___f_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object* v_m_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_matcherName_2206_, lean_object* v_info_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Meta_Match_addMatcherInfo___redArg(v_inst_2205_, v_matcherName_2206_, v_info_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___boxed(lean_object* v_m_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_matcherName_2212_, lean_object* v_info_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Meta_Match_addMatcherInfo(v_m_2209_, v_inst_2210_, v_inst_2211_, v_matcherName_2212_, v_info_2213_);
lean_dec_ref(v_inst_2210_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfoCore_x3f(lean_object* v_env_2215_, lean_object* v_declName_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2215_, v_declName_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(lean_object* v_declName_2218_, lean_object* v_toPure_2219_, lean_object* v_____do__lift_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_____do__lift_2220_, v_declName_2218_);
v___x_2222_ = lean_apply_2(v_toPure_2219_, lean_box(0), v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_declName_2225_){
_start:
{
lean_object* v_toApplicative_2226_; lean_object* v_toBind_2227_; lean_object* v_getEnv_2228_; lean_object* v_toPure_2229_; lean_object* v___f_2230_; lean_object* v___x_2231_; 
v_toApplicative_2226_ = lean_ctor_get(v_inst_2223_, 0);
lean_inc_ref(v_toApplicative_2226_);
v_toBind_2227_ = lean_ctor_get(v_inst_2223_, 1);
lean_inc(v_toBind_2227_);
lean_dec_ref(v_inst_2223_);
v_getEnv_2228_ = lean_ctor_get(v_inst_2224_, 0);
lean_inc(v_getEnv_2228_);
lean_dec_ref(v_inst_2224_);
v_toPure_2229_ = lean_ctor_get(v_toApplicative_2226_, 1);
lean_inc(v_toPure_2229_);
lean_dec_ref(v_toApplicative_2226_);
v___f_2230_ = lean_alloc_closure((void*)(l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2230_, 0, v_declName_2225_);
lean_closure_set(v___f_2230_, 1, v_toPure_2229_);
v___x_2231_ = lean_apply_4(v_toBind_2227_, lean_box(0), lean_box(0), v_getEnv_2228_, v___f_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object* v_m_2232_, lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_declName_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_2233_, v_inst_2234_, v_declName_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherCore(lean_object* v_env_2237_, lean_object* v_declName_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2237_, v_declName_2238_);
if (lean_obj_tag(v___x_2239_) == 0)
{
uint8_t v___x_2240_; 
v___x_2240_ = 0;
return v___x_2240_;
}
else
{
uint8_t v___x_2241_; 
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = 1;
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherCore___boxed(lean_object* v_env_2242_, lean_object* v_declName_2243_){
_start:
{
uint8_t v_res_2244_; lean_object* v_r_2245_; 
v_res_2244_ = l_Lean_Meta_isMatcherCore(v_env_2242_, v_declName_2243_);
v_r_2245_ = lean_box(v_res_2244_);
return v_r_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg___lam__0(lean_object* v_declName_2246_, lean_object* v_toPure_2247_, lean_object* v_____do__lift_2248_){
_start:
{
uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = l_Lean_Meta_isMatcherCore(v_____do__lift_2248_, v_declName_2246_);
v___x_2250_ = lean_box(v___x_2249_);
v___x_2251_ = lean_apply_2(v_toPure_2247_, lean_box(0), v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg(lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_declName_2254_){
_start:
{
lean_object* v_toApplicative_2255_; lean_object* v_toBind_2256_; lean_object* v_getEnv_2257_; lean_object* v_toPure_2258_; lean_object* v___f_2259_; lean_object* v___x_2260_; 
v_toApplicative_2255_ = lean_ctor_get(v_inst_2252_, 0);
lean_inc_ref(v_toApplicative_2255_);
v_toBind_2256_ = lean_ctor_get(v_inst_2252_, 1);
lean_inc(v_toBind_2256_);
lean_dec_ref(v_inst_2252_);
v_getEnv_2257_ = lean_ctor_get(v_inst_2253_, 0);
lean_inc(v_getEnv_2257_);
lean_dec_ref(v_inst_2253_);
v_toPure_2258_ = lean_ctor_get(v_toApplicative_2255_, 1);
lean_inc(v_toPure_2258_);
lean_dec_ref(v_toApplicative_2255_);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcher___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2259_, 0, v_declName_2254_);
lean_closure_set(v___f_2259_, 1, v_toPure_2258_);
v___x_2260_ = lean_apply_4(v_toBind_2256_, lean_box(0), lean_box(0), v_getEnv_2257_, v___f_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher(lean_object* v_m_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_declName_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_isMatcher___redArg(v_inst_2262_, v_inst_2263_, v_declName_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object* v_env_2266_, lean_object* v_e_2267_){
_start:
{
lean_object* v_fn_2268_; uint8_t v___x_2269_; 
v_fn_2268_ = l_Lean_Expr_getAppFn(v_e_2267_);
v___x_2269_ = l_Lean_Expr_isConst(v_fn_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
lean_dec_ref(v_fn_2268_);
lean_dec_ref(v_env_2266_);
v___x_2270_ = lean_box(0);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = l_Lean_Expr_constName_x21(v_fn_2268_);
lean_dec_ref(v_fn_2268_);
v___x_2272_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2266_, v___x_2271_);
if (lean_obj_tag(v___x_2272_) == 1)
{
lean_object* v_val_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_val_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_val_2273_);
v___x_2274_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2273_);
lean_dec(v_val_2273_);
v___x_2275_ = l_Lean_Expr_getAppNumArgs(v_e_2267_);
v___x_2276_ = lean_nat_dec_le(v___x_2274_, v___x_2275_);
lean_dec(v___x_2275_);
lean_dec(v___x_2274_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_dec_ref_known(v___x_2272_, 1);
v___x_2277_ = lean_box(0);
return v___x_2277_;
}
else
{
return v___x_2272_;
}
}
else
{
lean_object* v___x_2278_; 
lean_dec(v___x_2272_);
v___x_2278_ = lean_box(0);
return v___x_2278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f___boxed(lean_object* v_env_2279_, lean_object* v_e_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2279_, v_e_2280_);
lean_dec_ref(v_e_2280_);
return v_res_2281_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherAppCore(lean_object* v_env_2282_, lean_object* v_e_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2282_, v_e_2283_);
if (lean_obj_tag(v___x_2284_) == 0)
{
uint8_t v___x_2285_; 
v___x_2285_ = 0;
return v___x_2285_;
}
else
{
uint8_t v___x_2286_; 
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = 1;
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore___boxed(lean_object* v_env_2287_, lean_object* v_e_2288_){
_start:
{
uint8_t v_res_2289_; lean_object* v_r_2290_; 
v_res_2289_ = l_Lean_Meta_isMatcherAppCore(v_env_2287_, v_e_2288_);
lean_dec_ref(v_e_2288_);
v_r_2290_ = lean_box(v_res_2289_);
return v_r_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0(lean_object* v_e_2291_, lean_object* v_toPure_2292_, lean_object* v_____do__lift_2293_){
_start:
{
uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = l_Lean_Meta_isMatcherAppCore(v_____do__lift_2293_, v_e_2291_);
v___x_2295_ = lean_box(v___x_2294_);
v___x_2296_ = lean_apply_2(v_toPure_2292_, lean_box(0), v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(lean_object* v_e_2297_, lean_object* v_toPure_2298_, lean_object* v_____do__lift_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Meta_isMatcherApp___redArg___lam__0(v_e_2297_, v_toPure_2298_, v_____do__lift_2299_);
lean_dec_ref(v_e_2297_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg(lean_object* v_inst_2301_, lean_object* v_inst_2302_, lean_object* v_e_2303_){
_start:
{
lean_object* v_toApplicative_2304_; lean_object* v_toBind_2305_; lean_object* v_getEnv_2306_; lean_object* v_toPure_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
v_toApplicative_2304_ = lean_ctor_get(v_inst_2301_, 0);
lean_inc_ref(v_toApplicative_2304_);
v_toBind_2305_ = lean_ctor_get(v_inst_2301_, 1);
lean_inc(v_toBind_2305_);
lean_dec_ref(v_inst_2301_);
v_getEnv_2306_ = lean_ctor_get(v_inst_2302_, 0);
lean_inc(v_getEnv_2306_);
lean_dec_ref(v_inst_2302_);
v_toPure_2307_ = lean_ctor_get(v_toApplicative_2304_, 1);
lean_inc(v_toPure_2307_);
lean_dec_ref(v_toApplicative_2304_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2308_, 0, v_e_2303_);
lean_closure_set(v___f_2308_, 1, v_toPure_2307_);
v___x_2309_ = lean_apply_4(v_toBind_2305_, lean_box(0), lean_box(0), v_getEnv_2306_, v___f_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp(lean_object* v_m_2310_, lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_e_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Meta_isMatcherApp___redArg(v_inst_2311_, v_inst_2312_, v_e_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_));
v___x_2322_ = lean_box(0);
v___x_2323_ = l_Lean_mkTagDeclarationExtension(v___x_2321_, v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markMatcherLike(lean_object* v_env_2326_, lean_object* v_declName_2327_){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = l_Lean_Meta_matcherLikeExt;
v___x_2329_ = l_Lean_TagDeclarationExtension_tag(v___x_2328_, v_env_2326_, v_declName_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isMatcherLikeCore(lean_object* v_env_2330_, lean_object* v_declName_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v_toEnvExtension_2333_; lean_object* v_asyncMode_2334_; uint8_t v___x_2335_; 
v___x_2332_ = l_Lean_Meta_matcherLikeExt;
v_toEnvExtension_2333_ = lean_ctor_get(v___x_2332_, 0);
v_asyncMode_2334_ = lean_ctor_get(v_toEnvExtension_2333_, 2);
v___x_2335_ = l_Lean_TagDeclarationExtension_isTagged(v___x_2332_, v_env_2330_, v_declName_2331_, v_asyncMode_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLikeCore___boxed(lean_object* v_env_2336_, lean_object* v_declName_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_Lean_Meta_isMatcherLikeCore(v_env_2336_, v_declName_2337_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg___lam__0(lean_object* v_declName_2340_, lean_object* v_toPure_2341_, lean_object* v_____do__lift_2342_){
_start:
{
uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = l_Lean_Meta_isMatcherLikeCore(v_____do__lift_2342_, v_declName_2340_);
v___x_2344_ = lean_box(v___x_2343_);
v___x_2345_ = lean_apply_2(v_toPure_2341_, lean_box(0), v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg(lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_declName_2348_){
_start:
{
lean_object* v_toApplicative_2349_; lean_object* v_toBind_2350_; lean_object* v_getEnv_2351_; lean_object* v_toPure_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; 
v_toApplicative_2349_ = lean_ctor_get(v_inst_2346_, 0);
lean_inc_ref(v_toApplicative_2349_);
v_toBind_2350_ = lean_ctor_get(v_inst_2346_, 1);
lean_inc(v_toBind_2350_);
lean_dec_ref(v_inst_2346_);
v_getEnv_2351_ = lean_ctor_get(v_inst_2347_, 0);
lean_inc(v_getEnv_2351_);
lean_dec_ref(v_inst_2347_);
v_toPure_2352_ = lean_ctor_get(v_toApplicative_2349_, 1);
lean_inc(v_toPure_2352_);
lean_dec_ref(v_toApplicative_2349_);
v___f_2353_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherLike___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2353_, 0, v_declName_2348_);
lean_closure_set(v___f_2353_, 1, v_toPure_2352_);
v___x_2354_ = lean_apply_4(v_toBind_2350_, lean_box(0), lean_box(0), v_getEnv_2351_, v___f_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike(lean_object* v_m_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_declName_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Meta_isMatcherLike___redArg(v_inst_2356_, v_inst_2357_, v_declName_2358_);
return v___x_2359_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Match_instInhabitedDiscrInfo_default = _init_l_Lean_Meta_Match_instInhabitedDiscrInfo_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo_default);
l_Lean_Meta_Match_instInhabitedDiscrInfo = _init_l_Lean_Meta_Match_instInhabitedDiscrInfo();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedDiscrInfo);
l_Lean_Meta_Match_instInhabitedOverlaps_default = _init_l_Lean_Meta_Match_instInhabitedOverlaps_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps_default);
l_Lean_Meta_Match_instInhabitedOverlaps = _init_l_Lean_Meta_Match_instInhabitedOverlaps();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedOverlaps);
l_Lean_Meta_Match_instInhabitedMatcherInfo_default = _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo_default);
l_Lean_Meta_Match_instInhabitedMatcherInfo = _init_l_Lean_Meta_Match_instInhabitedMatcherInfo();
lean_mark_persistent(l_Lean_Meta_Match_instInhabitedMatcherInfo);
l_Lean_Meta_Match_Extension_instInhabitedState = _init_l_Lean_Meta_Match_Extension_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Match_Extension_instInhabitedState);
res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_207521612____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Match_Extension_extension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Match_Extension_extension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_matcherLikeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_matcherLikeExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_MatcherInfo(builtin);
}
#ifdef __cplusplus
}
#endif
