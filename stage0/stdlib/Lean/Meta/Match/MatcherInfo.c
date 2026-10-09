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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
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
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_logDeclChange(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Extension"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "extension"};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__5_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 134, 186, 123, 61, 240, 95, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__6_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 199, 90, 164, 66, 112, 193, 41)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__7_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 71, 76, 183, 128, 212, 252, 252)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_Extension_State_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__8_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__9_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__10_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__11_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_extension;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo___lam__0(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__3_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__4_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(lean_object* v_as_90_, size_t v_i_91_, size_t v_stop_92_, lean_object* v_b_93_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_90_ = stack[0].m_obj;
size_t v_i_91_ = stack[1].m_num;
size_t v_stop_92_ = stack[2].m_num;
lean_object* v_b_93_ = stack[3].m_obj;
lean_object* v_res_100_;
v_res_100_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_as_90_, v_i_91_, v_stop_92_, v_b_93_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2___boxed(lean_object* v_as_101_, lean_object* v_i_102_, lean_object* v_stop_103_, lean_object* v_b_104_){
_start:
{
size_t v_i_boxed_105_; size_t v_stop_boxed_106_; lean_object* v_res_107_; 
v_i_boxed_105_ = lean_unbox_usize(v_i_102_);
lean_dec(v_i_102_);
v_stop_boxed_106_ = lean_unbox_usize(v_stop_103_);
lean_dec(v_stop_103_);
v_res_107_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_as_101_, v_i_boxed_105_, v_stop_boxed_106_, v_b_104_);
lean_dec_ref(v_as_101_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 0)
{
lean_dec(v_x_108_);
return v_x_109_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_123_; 
v_head_111_ = lean_ctor_get(v_x_110_, 0);
v_tail_112_ = lean_ctor_get(v_x_110_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_110_);
if (v_isSharedCheck_123_ == 0)
{
v___x_114_ = v_x_110_;
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_tail_112_);
lean_inc(v_head_111_);
lean_dec(v_x_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
lean_inc(v_x_108_);
if (v_isShared_115_ == 0)
{
lean_ctor_set_tag(v___x_114_, 5);
lean_ctor_set(v___x_114_, 1, v_x_108_);
lean_ctor_set(v___x_114_, 0, v_x_109_);
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_x_109_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_x_108_);
v___x_117_ = v_reuseFailAlloc_122_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = l_Nat_reprFast(v_head_111_);
v___x_119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_117_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v_x_109_ = v___x_120_;
v_x_110_ = v_tail_112_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_dec(v_x_124_);
return v_x_125_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_139_; 
v_head_127_ = lean_ctor_get(v_x_126_, 0);
v_tail_128_ = lean_ctor_get(v_x_126_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_126_);
if (v_isSharedCheck_139_ == 0)
{
v___x_130_ = v_x_126_;
v_isShared_131_ = v_isSharedCheck_139_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_tail_128_);
lean_inc(v_head_127_);
lean_dec(v_x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_139_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
lean_inc(v_x_124_);
if (v_isShared_131_ == 0)
{
lean_ctor_set_tag(v___x_130_, 5);
lean_ctor_set(v___x_130_, 1, v_x_124_);
lean_ctor_set(v___x_130_, 0, v_x_125_);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_x_125_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_x_124_);
v___x_133_ = v_reuseFailAlloc_138_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = l_Nat_reprFast(v_head_127_);
v___x_135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_133_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7_spec__10(v_x_124_, v___x_136_, v_tail_128_);
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l_Nat_reprFast(v___y_140_);
v___x_142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
lean_object* v___x_145_; 
lean_dec(v_x_144_);
v___x_145_ = lean_box(0);
return v___x_145_;
}
else
{
lean_object* v_tail_146_; 
v_tail_146_ = lean_ctor_get(v_x_143_, 1);
if (lean_obj_tag(v_tail_146_) == 0)
{
lean_object* v_head_147_; lean_object* v___x_148_; 
lean_dec(v_x_144_);
v_head_147_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_head_147_);
lean_dec_ref_known(v_x_143_, 2);
v___x_148_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_147_);
return v___x_148_;
}
else
{
lean_object* v_head_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_inc(v_tail_146_);
v_head_149_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_head_149_);
lean_dec_ref_known(v_x_143_, 2);
v___x_150_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_149_);
v___x_151_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5_spec__7(v_x_144_, v___x_150_, v_tail_146_);
return v___x_151_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_164_ = lean_string_length(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__7);
v___x_166_ = lean_nat_to_int(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_a_171_){
_start:
{
if (lean_obj_tag(v_a_171_) == 0)
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1));
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; 
v___x_173_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_174_ = l_Std_Format_joinSep___at___00List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2_spec__5(v_a_171_, v___x_173_);
v___x_175_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
v___x_176_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9));
v___x_177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_174_);
v___x_178_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_175_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = 0;
v___x_182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*1, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
lean_dec(v_x_183_);
return v_x_184_;
}
else
{
lean_object* v_head_186_; lean_object* v_tail_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_196_; 
v_head_186_ = lean_ctor_get(v_x_185_, 0);
v_tail_187_ = lean_ctor_get(v_x_185_, 1);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_185_);
if (v_isSharedCheck_196_ == 0)
{
v___x_189_ = v_x_185_;
v_isShared_190_ = v_isSharedCheck_196_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_tail_187_);
lean_inc(v_head_186_);
lean_dec(v_x_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_196_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
lean_inc(v_x_183_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 5);
lean_ctor_set(v___x_189_, 1, v_x_183_);
lean_ctor_set(v___x_189_, 0, v_x_184_);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_x_184_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_x_183_);
v___x_192_ = v_reuseFailAlloc_195_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_head_186_);
v_x_184_ = v___x_193_;
v_x_185_ = v_tail_187_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_199_; 
lean_dec(v_x_198_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
lean_object* v_tail_200_; 
v_tail_200_ = lean_ctor_get(v_x_197_, 1);
if (lean_obj_tag(v_tail_200_) == 0)
{
lean_object* v_head_201_; 
lean_dec(v_x_198_);
v_head_201_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_head_201_);
lean_dec_ref_known(v_x_197_, 2);
return v_head_201_;
}
else
{
lean_object* v_head_202_; lean_object* v___x_203_; 
lean_inc(v_tail_200_);
v_head_202_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_head_202_);
lean_dec_ref_known(v_x_197_, 2);
v___x_203_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3_spec__7(v_x_198_, v_head_202_, v_tail_200_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(lean_object* v_init_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v_k_206_; lean_object* v_l_207_; lean_object* v_r_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_k_206_ = lean_ctor_get(v_x_205_, 1);
v_l_207_ = lean_ctor_get(v_x_205_, 3);
v_r_208_ = lean_ctor_get(v_x_205_, 4);
v___x_209_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_204_, v_r_208_);
lean_inc(v_k_206_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v_k_206_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v_init_204_ = v___x_210_;
v_x_205_ = v_l_207_;
goto _start;
}
else
{
return v_init_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_init_212_, lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v_init_212_, v_x_213_);
lean_dec(v_x_213_);
return v_res_214_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__0));
v___x_221_ = lean_string_length(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__4);
v___x_223_ = lean_nat_to_int(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(lean_object* v_x_228_){
_start:
{
lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_258_; 
v_fst_229_ = lean_ctor_get(v_x_228_, 0);
v_snd_230_ = lean_ctor_get(v_x_228_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_258_ == 0)
{
v___x_232_ = v_x_228_;
v_isShared_233_ = v_isSharedCheck_258_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snd_230_);
lean_inc(v_fst_229_);
lean_dec(v_x_228_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_258_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_234_ = l_Nat_reprFast(v_fst_229_);
v___x_235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_box(0);
if (v_isShared_233_ == 0)
{
lean_ctor_set_tag(v___x_232_, 1);
lean_ctor_set(v___x_232_, 1, v___x_236_);
lean_ctor_set(v___x_232_, 0, v___x_235_);
v___x_238_ = v___x_232_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_257_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__2));
v___x_241_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__1(v___x_236_, v_snd_230_);
lean_dec(v_snd_230_);
v___x_242_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v___x_241_);
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_240_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Repr_addAppParen(v___x_243_, v___x_239_);
v___x_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_238_);
v___x_246_ = l_List_reverse___redArg(v___x_245_);
v___x_247_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_248_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__3(v___x_246_, v___x_247_);
v___x_249_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__5);
v___x_250_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__6));
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_248_);
v___x_252_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg___closed__7));
v___x_253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_249_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = 0;
v___x_256_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*1, v___x_255_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_dec(v_x_259_);
return v_x_260_;
}
else
{
lean_object* v_head_262_; lean_object* v_tail_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
v_head_262_ = lean_ctor_get(v_x_261_, 0);
v_tail_263_ = lean_ctor_get(v_x_261_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_273_ == 0)
{
v___x_265_ = v_x_261_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_tail_263_);
lean_inc(v_head_262_);
lean_dec(v_x_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
lean_inc(v_x_259_);
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 5);
lean_ctor_set(v___x_265_, 1, v_x_259_);
lean_ctor_set(v___x_265_, 0, v_x_260_);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_x_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_x_259_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_262_);
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v_x_260_ = v___x_270_;
v_x_261_ = v_tail_263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_dec(v_x_274_);
return v_x_275_;
}
else
{
lean_object* v_head_277_; lean_object* v_tail_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_288_; 
v_head_277_ = lean_ctor_get(v_x_276_, 0);
v_tail_278_ = lean_ctor_get(v_x_276_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_288_ == 0)
{
v___x_280_ = v_x_276_;
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_tail_278_);
lean_inc(v_head_277_);
lean_dec(v_x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
lean_inc(v_x_274_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 5);
lean_ctor_set(v___x_280_, 1, v_x_274_);
lean_ctor_set(v___x_280_, 0, v_x_275_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_x_275_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_x_274_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_277_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5_spec__10(v_x_274_, v___x_285_, v_tail_278_);
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_289_) == 0)
{
lean_object* v___x_291_; 
lean_dec(v_x_290_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
else
{
lean_object* v_tail_292_; 
v_tail_292_ = lean_ctor_get(v_x_289_, 1);
if (lean_obj_tag(v_tail_292_) == 0)
{
lean_object* v_head_293_; lean_object* v___x_294_; 
lean_dec(v_x_290_);
v_head_293_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_head_293_);
lean_dec_ref_known(v_x_289_, 2);
v___x_294_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_293_);
return v___x_294_;
}
else
{
lean_object* v_head_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_inc(v_tail_292_);
v_head_295_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_head_295_);
lean_dec_ref_known(v_x_289_, 2);
v___x_296_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_head_295_);
v___x_297_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1_spec__5(v_x_290_, v___x_296_, v_tail_292_);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(lean_object* v_a_298_){
_start:
{
if (lean_obj_tag(v_a_298_) == 0)
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__1));
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; 
v___x_300_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_301_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__1(v_a_298_, v___x_300_);
v___x_302_ = lean_obj_once(&l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8, &l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8_once, _init_l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__8);
v___x_303_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__9));
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_301_);
v___x_305_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_302_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = 0;
v___x_309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*1, v___x_308_);
return v___x_309_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(7u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___redArg(lean_object* v_x_324_){
_start:
{
lean_object* v_buckets_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_357_; 
v_buckets_325_ = lean_ctor_get(v_x_324_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v_x_324_, 0);
lean_dec(v_unused_358_);
v___x_327_ = v_x_324_;
v_isShared_328_ = v_isSharedCheck_357_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_buckets_325_);
lean_dec(v_x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_357_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___y_334_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_329_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__3));
v___x_330_ = lean_obj_once(&l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__4);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = ((lean_object*)(l_Lean_Meta_Match_instReprOverlaps_repr___redArg___closed__6));
v___x_351_ = lean_box(0);
v___x_352_ = lean_array_get_size(v_buckets_325_);
v___x_353_ = lean_nat_dec_lt(v___x_331_, v___x_352_);
if (v___x_353_ == 0)
{
lean_dec_ref(v_buckets_325_);
v___y_334_ = v___x_351_;
goto v___jp_333_;
}
else
{
size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_usize_of_nat(v___x_352_);
v___x_355_ = ((size_t)0ULL);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__2(v_buckets_325_, v___x_354_, v___x_355_, v___x_351_);
lean_dec_ref(v_buckets_325_);
v___y_334_ = v___x_356_;
goto v___jp_333_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v___y_334_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 5);
lean_ctor_set(v___x_327_, 1, v___x_335_);
lean_ctor_set(v___x_327_, 0, v___x_332_);
v___x_337_ = v___x_327_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_350_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_338_ = l_Repr_addAppParen(v___x_337_, v___x_331_);
v___x_339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_330_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = 0;
v___x_341_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*1, v___x_340_);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_329_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_344_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_342_);
v___x_346_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_343_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*1, v___x_340_);
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr(lean_object* v_x_359_, lean_object* v_prec_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_x_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprOverlaps_repr___boxed(lean_object* v_x_362_, lean_object* v_prec_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Match_instReprOverlaps_repr(v_x_362_, v_prec_363_);
lean_dec(v_prec_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(lean_object* v_a_365_, lean_object* v_n_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___redArg(v_a_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0___boxed(lean_object* v_a_368_, lean_object* v_n_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0(v_a_368_, v_n_369_);
lean_dec(v_n_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___redArg(v_x_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0___boxed(lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0(v_x_374_, v_x_375_);
lean_dec(v_x_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(lean_object* v_a_377_, lean_object* v_n_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg(v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_a_380_, lean_object* v_n_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2(v_a_380_, v_n_381_);
lean_dec(v_n_381_);
return v_res_382_;
}
}
uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object* v_o_385_){
_start:
{
lean_object* v_size_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_size_386_ = lean_ctor_get(v_o_385_, 0);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_nat_dec_eq(v_size_386_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_Overlaps_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_385_ = stack[0].m_obj;
uint8_t v_res_389_;
v_res_389_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_o_385_);
stack->m_num = v_res_389_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_isEmpty___boxed(lean_object* v_o_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_o_390_);
lean_dec_ref(v_o_390_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(lean_object* v_k_393_, lean_object* v_t_394_){
_start:
{
if (lean_obj_tag(v_t_394_) == 0)
{
lean_object* v_k_395_; lean_object* v_l_396_; lean_object* v_r_397_; uint8_t v___x_398_; 
v_k_395_ = lean_ctor_get(v_t_394_, 1);
v_l_396_ = lean_ctor_get(v_t_394_, 3);
v_r_397_ = lean_ctor_get(v_t_394_, 4);
v___x_398_ = lean_nat_dec_lt(v_k_393_, v_k_395_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
v___x_399_ = lean_nat_dec_eq(v_k_393_, v_k_395_);
if (v___x_399_ == 0)
{
v_t_394_ = v_r_397_;
goto _start;
}
else
{
return v___x_399_;
}
}
else
{
v_t_394_ = v_l_396_;
goto _start;
}
}
else
{
uint8_t v___x_402_; 
v___x_402_ = 0;
return v___x_402_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_393_ = stack[0].m_obj;
lean_object* v_t_394_ = stack[1].m_obj;
uint8_t v_res_403_;
v_res_403_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_393_, v_t_394_);
stack->m_num = v_res_403_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg___boxed(lean_object* v_k_404_, lean_object* v_t_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_404_, v_t_405_);
lean_dec(v_t_405_);
lean_dec(v_k_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(lean_object* v_k_408_, lean_object* v_v_409_, lean_object* v_t_410_){
_start:
{
if (lean_obj_tag(v_t_410_) == 0)
{
lean_object* v_size_411_; lean_object* v_k_412_; lean_object* v_v_413_; lean_object* v_l_414_; lean_object* v_r_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_696_; 
v_size_411_ = lean_ctor_get(v_t_410_, 0);
v_k_412_ = lean_ctor_get(v_t_410_, 1);
v_v_413_ = lean_ctor_get(v_t_410_, 2);
v_l_414_ = lean_ctor_get(v_t_410_, 3);
v_r_415_ = lean_ctor_get(v_t_410_, 4);
v_isSharedCheck_696_ = !lean_is_exclusive(v_t_410_);
if (v_isSharedCheck_696_ == 0)
{
v___x_417_ = v_t_410_;
v_isShared_418_ = v_isSharedCheck_696_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_r_415_);
lean_inc(v_l_414_);
lean_inc(v_v_413_);
lean_inc(v_k_412_);
lean_inc(v_size_411_);
lean_dec(v_t_410_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_696_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint8_t v___x_419_; 
v___x_419_ = lean_nat_dec_lt(v_k_408_, v_k_412_);
if (v___x_419_ == 0)
{
uint8_t v___x_420_; 
v___x_420_ = lean_nat_dec_eq(v_k_408_, v_k_412_);
if (v___x_420_ == 0)
{
lean_object* v_impl_421_; lean_object* v___x_422_; 
lean_dec(v_size_411_);
v_impl_421_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_408_, v_v_409_, v_r_415_);
v___x_422_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_414_) == 0)
{
lean_object* v_size_423_; lean_object* v_size_424_; lean_object* v_k_425_; lean_object* v_v_426_; lean_object* v_l_427_; lean_object* v_r_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_size_423_ = lean_ctor_get(v_l_414_, 0);
v_size_424_ = lean_ctor_get(v_impl_421_, 0);
v_k_425_ = lean_ctor_get(v_impl_421_, 1);
v_v_426_ = lean_ctor_get(v_impl_421_, 2);
v_l_427_ = lean_ctor_get(v_impl_421_, 3);
lean_inc(v_l_427_);
v_r_428_ = lean_ctor_get(v_impl_421_, 4);
v___x_429_ = lean_unsigned_to_nat(3u);
v___x_430_ = lean_nat_mul(v___x_429_, v_size_423_);
v___x_431_ = lean_nat_dec_lt(v___x_430_, v_size_424_);
lean_dec(v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
lean_dec(v_l_427_);
v___x_432_ = lean_nat_add(v___x_422_, v_size_423_);
v___x_433_ = lean_nat_add(v___x_432_, v_size_424_);
lean_dec(v___x_432_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_impl_421_);
lean_ctor_set(v___x_417_, 0, v___x_433_);
v___x_435_ = v___x_417_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_l_414_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_impl_421_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
else
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_500_; 
lean_inc(v_r_428_);
lean_inc(v_v_426_);
lean_inc(v_k_425_);
lean_inc(v_size_424_);
v_isSharedCheck_500_ = !lean_is_exclusive(v_impl_421_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; lean_object* v_unused_504_; lean_object* v_unused_505_; 
v_unused_501_ = lean_ctor_get(v_impl_421_, 4);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_impl_421_, 3);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_impl_421_, 2);
lean_dec(v_unused_503_);
v_unused_504_ = lean_ctor_get(v_impl_421_, 1);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_impl_421_, 0);
lean_dec(v_unused_505_);
v___x_438_ = v_impl_421_;
v_isShared_439_ = v_isSharedCheck_500_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_impl_421_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_500_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_size_440_; lean_object* v_k_441_; lean_object* v_v_442_; lean_object* v_l_443_; lean_object* v_r_444_; lean_object* v_size_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_size_440_ = lean_ctor_get(v_l_427_, 0);
v_k_441_ = lean_ctor_get(v_l_427_, 1);
v_v_442_ = lean_ctor_get(v_l_427_, 2);
v_l_443_ = lean_ctor_get(v_l_427_, 3);
v_r_444_ = lean_ctor_get(v_l_427_, 4);
v_size_445_ = lean_ctor_get(v_r_428_, 0);
v___x_446_ = lean_unsigned_to_nat(2u);
v___x_447_ = lean_nat_mul(v___x_446_, v_size_445_);
v___x_448_ = lean_nat_dec_lt(v_size_440_, v___x_447_);
lean_dec(v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_476_; 
lean_inc(v_r_444_);
lean_inc(v_l_443_);
lean_inc(v_v_442_);
lean_inc(v_k_441_);
v_isSharedCheck_476_ = !lean_is_exclusive(v_l_427_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; 
v_unused_477_ = lean_ctor_get(v_l_427_, 4);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_l_427_, 3);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_l_427_, 2);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_l_427_, 1);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_l_427_, 0);
lean_dec(v_unused_481_);
v___x_450_ = v_l_427_;
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
else
{
lean_dec(v_l_427_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_476_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_466_; 
v___x_452_ = lean_nat_add(v___x_422_, v_size_423_);
v___x_453_ = lean_nat_add(v___x_452_, v_size_424_);
lean_dec(v_size_424_);
if (lean_obj_tag(v_l_443_) == 0)
{
lean_object* v_size_474_; 
v_size_474_ = lean_ctor_get(v_l_443_, 0);
lean_inc(v_size_474_);
v___y_466_ = v_size_474_;
goto v___jp_465_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___y_466_ = v___x_475_;
goto v___jp_465_;
}
v___jp_454_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_nat_add(v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec(v___y_456_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 4, v_r_428_);
lean_ctor_set(v___x_450_, 3, v_r_444_);
lean_ctor_set(v___x_450_, 2, v_v_426_);
lean_ctor_set(v___x_450_, 1, v_k_425_);
lean_ctor_set(v___x_450_, 0, v___x_458_);
v___x_460_ = v___x_450_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_k_425_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_v_426_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_r_444_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_r_428_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 4, v___x_460_);
lean_ctor_set(v___x_438_, 3, v___y_455_);
lean_ctor_set(v___x_438_, 2, v_v_442_);
lean_ctor_set(v___x_438_, 1, v_k_441_);
lean_ctor_set(v___x_438_, 0, v___x_453_);
v___x_462_ = v___x_438_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_k_441_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_v_442_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v___y_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
v___jp_465_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_nat_add(v___x_452_, v___y_466_);
lean_dec(v___y_466_);
lean_dec(v___x_452_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_l_443_);
lean_ctor_set(v___x_417_, 0, v___x_467_);
v___x_469_ = v___x_417_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_l_414_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_l_443_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_nat_add(v___x_422_, v_size_445_);
if (lean_obj_tag(v_r_444_) == 0)
{
lean_object* v_size_471_; 
v_size_471_ = lean_ctor_get(v_r_444_, 0);
lean_inc(v_size_471_);
v___y_455_ = v___x_469_;
v___y_456_ = v___x_470_;
v___y_457_ = v_size_471_;
goto v___jp_454_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___y_455_ = v___x_469_;
v___y_456_ = v___x_470_;
v___y_457_ = v___x_472_;
goto v___jp_454_;
}
}
}
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
lean_del_object(v___x_417_);
v___x_482_ = lean_nat_add(v___x_422_, v_size_423_);
v___x_483_ = lean_nat_add(v___x_482_, v_size_424_);
lean_dec(v_size_424_);
v___x_484_ = lean_nat_add(v___x_482_, v_size_440_);
lean_dec(v___x_482_);
lean_inc_ref(v_l_414_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 4, v_l_427_);
lean_ctor_set(v___x_438_, 3, v_l_414_);
lean_ctor_set(v___x_438_, 2, v_v_413_);
lean_ctor_set(v___x_438_, 1, v_k_412_);
lean_ctor_set(v___x_438_, 0, v___x_484_);
v___x_486_ = v___x_438_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_l_414_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_l_427_);
v___x_486_ = v_reuseFailAlloc_499_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_isSharedCheck_493_ = !lean_is_exclusive(v_l_414_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; lean_object* v_unused_498_; 
v_unused_494_ = lean_ctor_get(v_l_414_, 4);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_l_414_, 3);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_l_414_, 2);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_l_414_, 1);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_l_414_, 0);
lean_dec(v_unused_498_);
v___x_488_ = v_l_414_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_dec(v_l_414_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_r_428_);
lean_ctor_set(v___x_488_, 3, v___x_486_);
lean_ctor_set(v___x_488_, 2, v_v_426_);
lean_ctor_set(v___x_488_, 1, v_k_425_);
lean_ctor_set(v___x_488_, 0, v___x_483_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_k_425_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_v_426_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_r_428_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_506_; 
v_l_506_ = lean_ctor_get(v_impl_421_, 3);
lean_inc(v_l_506_);
if (lean_obj_tag(v_l_506_) == 0)
{
lean_object* v_r_507_; lean_object* v_k_508_; lean_object* v_v_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_532_; 
v_r_507_ = lean_ctor_get(v_impl_421_, 4);
v_k_508_ = lean_ctor_get(v_impl_421_, 1);
v_v_509_ = lean_ctor_get(v_impl_421_, 2);
v_isSharedCheck_532_ = !lean_is_exclusive(v_impl_421_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; 
v_unused_533_ = lean_ctor_get(v_impl_421_, 3);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_impl_421_, 0);
lean_dec(v_unused_534_);
v___x_511_ = v_impl_421_;
v_isShared_512_ = v_isSharedCheck_532_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_r_507_);
lean_inc(v_v_509_);
lean_inc(v_k_508_);
lean_dec(v_impl_421_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_532_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_k_513_; lean_object* v_v_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_528_; 
v_k_513_ = lean_ctor_get(v_l_506_, 1);
v_v_514_ = lean_ctor_get(v_l_506_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v_l_506_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; 
v_unused_529_ = lean_ctor_get(v_l_506_, 4);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_l_506_, 3);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_l_506_, 0);
lean_dec(v_unused_531_);
v___x_516_ = v_l_506_;
v_isShared_517_ = v_isSharedCheck_528_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_v_514_);
lean_inc(v_k_513_);
lean_dec(v_l_506_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_528_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_507_, 2);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 4, v_r_507_);
lean_ctor_set(v___x_516_, 3, v_r_507_);
lean_ctor_set(v___x_516_, 2, v_v_413_);
lean_ctor_set(v___x_516_, 1, v_k_412_);
lean_ctor_set(v___x_516_, 0, v___x_422_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_r_507_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v_r_507_);
v___x_520_ = v_reuseFailAlloc_527_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
lean_inc(v_r_507_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 3, v_r_507_);
lean_ctor_set(v___x_511_, 0, v___x_422_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_k_508_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_v_509_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_r_507_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v_r_507_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v___x_522_);
lean_ctor_set(v___x_417_, 3, v___x_520_);
lean_ctor_set(v___x_417_, 2, v_v_514_);
lean_ctor_set(v___x_417_, 1, v_k_513_);
lean_ctor_set(v___x_417_, 0, v___x_518_);
v___x_524_ = v___x_417_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_k_513_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_v_514_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
else
{
lean_object* v_r_535_; 
v_r_535_ = lean_ctor_get(v_impl_421_, 4);
lean_inc(v_r_535_);
if (lean_obj_tag(v_r_535_) == 0)
{
lean_object* v_k_536_; lean_object* v_v_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
v_k_536_ = lean_ctor_get(v_impl_421_, 1);
v_v_537_ = lean_ctor_get(v_impl_421_, 2);
v_isSharedCheck_548_ = !lean_is_exclusive(v_impl_421_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_549_ = lean_ctor_get(v_impl_421_, 4);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_impl_421_, 3);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_impl_421_, 0);
lean_dec(v_unused_551_);
v___x_539_ = v_impl_421_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_v_537_);
lean_inc(v_k_536_);
lean_dec(v_impl_421_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_unsigned_to_nat(3u);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 4, v_l_506_);
lean_ctor_set(v___x_539_, 2, v_v_413_);
lean_ctor_set(v___x_539_, 1, v_k_412_);
lean_ctor_set(v___x_539_, 0, v___x_422_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_l_506_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_l_506_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_r_535_);
lean_ctor_set(v___x_417_, 3, v___x_543_);
lean_ctor_set(v___x_417_, 2, v_v_537_);
lean_ctor_set(v___x_417_, 1, v_k_536_);
lean_ctor_set(v___x_417_, 0, v___x_541_);
v___x_545_ = v___x_417_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_r_535_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_unsigned_to_nat(2u);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_impl_421_);
lean_ctor_set(v___x_417_, 3, v_r_535_);
lean_ctor_set(v___x_417_, 0, v___x_552_);
v___x_554_ = v___x_417_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_r_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_impl_421_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
else
{
lean_object* v___x_557_; 
lean_dec(v_v_413_);
lean_dec(v_k_412_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 2, v_v_409_);
lean_ctor_set(v___x_417_, 1, v_k_408_);
v___x_557_ = v___x_417_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_size_411_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_k_408_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_v_409_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_l_414_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_r_415_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_impl_559_; lean_object* v___x_560_; 
lean_dec(v_size_411_);
v_impl_559_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_408_, v_v_409_, v_l_414_);
v___x_560_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_415_) == 0)
{
lean_object* v_size_561_; lean_object* v_size_562_; lean_object* v_k_563_; lean_object* v_v_564_; lean_object* v_l_565_; lean_object* v_r_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_size_561_ = lean_ctor_get(v_r_415_, 0);
v_size_562_ = lean_ctor_get(v_impl_559_, 0);
v_k_563_ = lean_ctor_get(v_impl_559_, 1);
v_v_564_ = lean_ctor_get(v_impl_559_, 2);
v_l_565_ = lean_ctor_get(v_impl_559_, 3);
v_r_566_ = lean_ctor_get(v_impl_559_, 4);
lean_inc(v_r_566_);
v___x_567_ = lean_unsigned_to_nat(3u);
v___x_568_ = lean_nat_mul(v___x_567_, v_size_561_);
v___x_569_ = lean_nat_dec_lt(v___x_568_, v_size_562_);
lean_dec(v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec(v_r_566_);
v___x_570_ = lean_nat_add(v___x_560_, v_size_562_);
v___x_571_ = lean_nat_add(v___x_570_, v_size_561_);
lean_dec(v___x_570_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 3, v_impl_559_);
lean_ctor_set(v___x_417_, 0, v___x_571_);
v___x_573_ = v___x_417_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v_impl_559_);
lean_ctor_set(v_reuseFailAlloc_574_, 4, v_r_415_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_640_; 
lean_inc(v_l_565_);
lean_inc(v_v_564_);
lean_inc(v_k_563_);
lean_inc(v_size_562_);
v_isSharedCheck_640_ = !lean_is_exclusive(v_impl_559_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_641_ = lean_ctor_get(v_impl_559_, 4);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_impl_559_, 3);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_impl_559_, 2);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_impl_559_, 1);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_impl_559_, 0);
lean_dec(v_unused_645_);
v___x_576_ = v_impl_559_;
v_isShared_577_ = v_isSharedCheck_640_;
goto v_resetjp_575_;
}
else
{
lean_dec(v_impl_559_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_640_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_size_578_; lean_object* v_size_579_; lean_object* v_k_580_; lean_object* v_v_581_; lean_object* v_l_582_; lean_object* v_r_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_size_578_ = lean_ctor_get(v_l_565_, 0);
v_size_579_ = lean_ctor_get(v_r_566_, 0);
v_k_580_ = lean_ctor_get(v_r_566_, 1);
v_v_581_ = lean_ctor_get(v_r_566_, 2);
v_l_582_ = lean_ctor_get(v_r_566_, 3);
v_r_583_ = lean_ctor_get(v_r_566_, 4);
v___x_584_ = lean_unsigned_to_nat(2u);
v___x_585_ = lean_nat_mul(v___x_584_, v_size_578_);
v___x_586_ = lean_nat_dec_lt(v_size_579_, v___x_585_);
lean_dec(v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_615_; 
lean_inc(v_r_583_);
lean_inc(v_l_582_);
lean_inc(v_v_581_);
lean_inc(v_k_580_);
v_isSharedCheck_615_ = !lean_is_exclusive(v_r_566_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_616_ = lean_ctor_get(v_r_566_, 4);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_r_566_, 3);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_r_566_, 2);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_r_566_, 1);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_r_566_, 0);
lean_dec(v_unused_620_);
v___x_588_ = v_r_566_;
v_isShared_589_ = v_isSharedCheck_615_;
goto v_resetjp_587_;
}
else
{
lean_dec(v_r_566_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_615_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___x_603_; lean_object* v___y_605_; 
v___x_590_ = lean_nat_add(v___x_560_, v_size_562_);
lean_dec(v_size_562_);
v___x_591_ = lean_nat_add(v___x_590_, v_size_561_);
lean_dec(v___x_590_);
v___x_603_ = lean_nat_add(v___x_560_, v_size_578_);
if (lean_obj_tag(v_l_582_) == 0)
{
lean_object* v_size_613_; 
v_size_613_ = lean_ctor_get(v_l_582_, 0);
lean_inc(v_size_613_);
v___y_605_ = v_size_613_;
goto v___jp_604_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_unsigned_to_nat(0u);
v___y_605_ = v___x_614_;
goto v___jp_604_;
}
v___jp_592_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_nat_add(v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec(v___y_594_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 4, v_r_415_);
lean_ctor_set(v___x_588_, 3, v_r_583_);
lean_ctor_set(v___x_588_, 2, v_v_413_);
lean_ctor_set(v___x_588_, 1, v_k_412_);
lean_ctor_set(v___x_588_, 0, v___x_596_);
v___x_598_ = v___x_588_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_r_583_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_r_415_);
v___x_598_ = v_reuseFailAlloc_602_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_600_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v___x_598_);
lean_ctor_set(v___x_576_, 3, v___y_593_);
lean_ctor_set(v___x_576_, 2, v_v_581_);
lean_ctor_set(v___x_576_, 1, v_k_580_);
lean_ctor_set(v___x_576_, 0, v___x_591_);
v___x_600_ = v___x_576_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_k_580_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_v_581_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v___y_593_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_nat_add(v___x_603_, v___y_605_);
lean_dec(v___y_605_);
lean_dec(v___x_603_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_l_582_);
lean_ctor_set(v___x_417_, 3, v_l_565_);
lean_ctor_set(v___x_417_, 2, v_v_564_);
lean_ctor_set(v___x_417_, 1, v_k_563_);
lean_ctor_set(v___x_417_, 0, v___x_606_);
v___x_608_ = v___x_417_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_l_582_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_nat_add(v___x_560_, v_size_561_);
if (lean_obj_tag(v_r_583_) == 0)
{
lean_object* v_size_610_; 
v_size_610_ = lean_ctor_get(v_r_583_, 0);
lean_inc(v_size_610_);
v___y_593_ = v___x_608_;
v___y_594_ = v___x_609_;
v___y_595_ = v_size_610_;
goto v___jp_592_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___y_593_ = v___x_608_;
v___y_594_ = v___x_609_;
v___y_595_ = v___x_611_;
goto v___jp_592_;
}
}
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_del_object(v___x_417_);
v___x_621_ = lean_nat_add(v___x_560_, v_size_562_);
lean_dec(v_size_562_);
v___x_622_ = lean_nat_add(v___x_621_, v_size_561_);
lean_dec(v___x_621_);
v___x_623_ = lean_nat_add(v___x_560_, v_size_561_);
v___x_624_ = lean_nat_add(v___x_623_, v_size_579_);
lean_dec(v___x_623_);
lean_inc_ref(v_r_415_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v_r_415_);
lean_ctor_set(v___x_576_, 3, v_r_566_);
lean_ctor_set(v___x_576_, 2, v_v_413_);
lean_ctor_set(v___x_576_, 1, v_k_412_);
lean_ctor_set(v___x_576_, 0, v___x_624_);
v___x_626_ = v___x_576_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_r_566_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_r_415_);
v___x_626_ = v_reuseFailAlloc_639_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_isSharedCheck_633_ = !lean_is_exclusive(v_r_415_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_634_ = lean_ctor_get(v_r_415_, 4);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_r_415_, 3);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_r_415_, 2);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_r_415_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_r_415_, 0);
lean_dec(v_unused_638_);
v___x_628_ = v_r_415_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_r_415_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v___x_626_);
lean_ctor_set(v___x_628_, 3, v_l_565_);
lean_ctor_set(v___x_628_, 2, v_v_564_);
lean_ctor_set(v___x_628_, 1, v_k_563_);
lean_ctor_set(v___x_628_, 0, v___x_622_);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_563_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_v_564_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_l_565_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v___x_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_646_; 
v_l_646_ = lean_ctor_get(v_impl_559_, 3);
if (lean_obj_tag(v_l_646_) == 0)
{
lean_object* v_r_647_; lean_object* v_k_648_; lean_object* v_v_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_660_; 
lean_inc_ref(v_l_646_);
v_r_647_ = lean_ctor_get(v_impl_559_, 4);
v_k_648_ = lean_ctor_get(v_impl_559_, 1);
v_v_649_ = lean_ctor_get(v_impl_559_, 2);
v_isSharedCheck_660_ = !lean_is_exclusive(v_impl_559_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; lean_object* v_unused_662_; 
v_unused_661_ = lean_ctor_get(v_impl_559_, 3);
lean_dec(v_unused_661_);
v_unused_662_ = lean_ctor_get(v_impl_559_, 0);
lean_dec(v_unused_662_);
v___x_651_ = v_impl_559_;
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_r_647_);
lean_inc(v_v_649_);
lean_inc(v_k_648_);
lean_dec(v_impl_559_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_660_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_647_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 3, v_r_647_);
lean_ctor_set(v___x_651_, 2, v_v_413_);
lean_ctor_set(v___x_651_, 1, v_k_412_);
lean_ctor_set(v___x_651_, 0, v___x_560_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_r_647_);
lean_ctor_set(v_reuseFailAlloc_659_, 4, v_r_647_);
v___x_655_ = v_reuseFailAlloc_659_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v___x_655_);
lean_ctor_set(v___x_417_, 3, v_l_646_);
lean_ctor_set(v___x_417_, 2, v_v_649_);
lean_ctor_set(v___x_417_, 1, v_k_648_);
lean_ctor_set(v___x_417_, 0, v___x_653_);
v___x_657_ = v___x_417_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_k_648_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_v_649_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_l_646_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_r_663_; 
v_r_663_ = lean_ctor_get(v_impl_559_, 4);
lean_inc(v_r_663_);
if (lean_obj_tag(v_r_663_) == 0)
{
lean_object* v_k_664_; lean_object* v_v_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_688_; 
lean_inc(v_l_646_);
v_k_664_ = lean_ctor_get(v_impl_559_, 1);
v_v_665_ = lean_ctor_get(v_impl_559_, 2);
v_isSharedCheck_688_ = !lean_is_exclusive(v_impl_559_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_689_ = lean_ctor_get(v_impl_559_, 4);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_impl_559_, 3);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_impl_559_, 0);
lean_dec(v_unused_691_);
v___x_667_ = v_impl_559_;
v_isShared_668_ = v_isSharedCheck_688_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_v_665_);
lean_inc(v_k_664_);
lean_dec(v_impl_559_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_688_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_k_669_; lean_object* v_v_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_684_; 
v_k_669_ = lean_ctor_get(v_r_663_, 1);
v_v_670_ = lean_ctor_get(v_r_663_, 2);
v_isSharedCheck_684_ = !lean_is_exclusive(v_r_663_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; lean_object* v_unused_686_; lean_object* v_unused_687_; 
v_unused_685_ = lean_ctor_get(v_r_663_, 4);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_r_663_, 3);
lean_dec(v_unused_686_);
v_unused_687_ = lean_ctor_get(v_r_663_, 0);
lean_dec(v_unused_687_);
v___x_672_ = v_r_663_;
v_isShared_673_ = v_isSharedCheck_684_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_v_670_);
lean_inc(v_k_669_);
lean_dec(v_r_663_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_684_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(3u);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 4, v_l_646_);
lean_ctor_set(v___x_672_, 3, v_l_646_);
lean_ctor_set(v___x_672_, 2, v_v_665_);
lean_ctor_set(v___x_672_, 1, v_k_664_);
lean_ctor_set(v___x_672_, 0, v___x_560_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_k_664_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_v_665_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_l_646_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_l_646_);
v___x_676_ = v_reuseFailAlloc_683_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 4, v_l_646_);
lean_ctor_set(v___x_667_, 2, v_v_413_);
lean_ctor_set(v___x_667_, 1, v_k_412_);
lean_ctor_set(v___x_667_, 0, v___x_560_);
v___x_678_ = v___x_667_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_l_646_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_l_646_);
v___x_678_ = v_reuseFailAlloc_682_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v___x_678_);
lean_ctor_set(v___x_417_, 3, v___x_676_);
lean_ctor_set(v___x_417_, 2, v_v_670_);
lean_ctor_set(v___x_417_, 1, v_k_669_);
lean_ctor_set(v___x_417_, 0, v___x_674_);
v___x_680_ = v___x_417_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_k_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_v_670_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
else
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = lean_unsigned_to_nat(2u);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_r_663_);
lean_ctor_set(v___x_417_, 3, v_impl_559_);
lean_ctor_set(v___x_417_, 0, v___x_692_);
v___x_694_ = v___x_417_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_412_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_413_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_impl_559_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_r_663_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_k_408_);
lean_ctor_set(v___x_698_, 2, v_v_409_);
lean_ctor_set(v___x_698_, 3, v_t_410_);
lean_ctor_set(v___x_698_, 4, v_t_410_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(lean_object* v_overlapping_699_, lean_object* v_s_x3f_700_){
_start:
{
lean_object* v___y_702_; 
if (lean_obj_tag(v_s_x3f_700_) == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(1);
v___y_702_ = v___x_708_;
goto v___jp_701_;
}
else
{
lean_object* v_val_709_; 
v_val_709_ = lean_ctor_get(v_s_x3f_700_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_s_x3f_700_, 1);
v___y_702_ = v_val_709_;
goto v___jp_701_;
}
v___jp_701_:
{
uint8_t v___x_703_; 
v___x_703_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_699_, v___y_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_box(0);
v___x_705_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_699_, v___x_704_, v___y_702_);
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; 
lean_dec(v_overlapping_699_);
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v___y_702_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(lean_object* v_overlapping_710_, lean_object* v_a_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_val_715_; lean_object* v___x_716_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_710_, v___x_713_);
v_val_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_val_715_);
lean_dec(v___x_714_);
v___x_716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_716_, 0, v_a_711_);
lean_ctor_set(v___x_716_, 1, v_val_715_);
lean_ctor_set(v___x_716_, 2, v_x_712_);
return v___x_716_;
}
else
{
lean_object* v_key_717_; lean_object* v_value_718_; lean_object* v_tail_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_734_; 
v_key_717_ = lean_ctor_get(v_x_712_, 0);
v_value_718_ = lean_ctor_get(v_x_712_, 1);
v_tail_719_ = lean_ctor_get(v_x_712_, 2);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_734_ == 0)
{
v___x_721_ = v_x_712_;
v_isShared_722_ = v_isSharedCheck_734_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_tail_719_);
lean_inc(v_value_718_);
lean_inc(v_key_717_);
lean_dec(v_x_712_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_734_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
uint8_t v___x_723_; 
v___x_723_ = lean_nat_dec_eq(v_key_717_, v_a_711_);
if (v___x_723_ == 0)
{
lean_object* v_tail_724_; lean_object* v___x_726_; 
v_tail_724_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_710_, v_a_711_, v_tail_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 2, v_tail_724_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_key_717_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_value_718_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_tail_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_val_730_; lean_object* v___x_732_; 
lean_dec(v_key_717_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_value_718_);
v___x_729_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4___lam__0(v_overlapping_710_, v___x_728_);
v_val_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_730_);
lean_dec(v___x_729_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v_val_730_);
lean_ctor_set(v___x_721_, 0, v_a_711_);
v___x_732_ = v___x_721_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_711_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_val_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_tail_719_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(lean_object* v_a_735_, lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_736_) == 0)
{
uint8_t v___x_737_; 
v___x_737_ = 0;
return v___x_737_;
}
else
{
lean_object* v_key_738_; lean_object* v_tail_739_; uint8_t v___x_740_; 
v_key_738_ = lean_ctor_get(v_x_736_, 0);
v_tail_739_ = lean_ctor_get(v_x_736_, 2);
v___x_740_ = lean_nat_dec_eq(v_key_738_, v_a_735_);
if (v___x_740_ == 0)
{
v_x_736_ = v_tail_739_;
goto _start;
}
else
{
return v___x_740_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_735_ = stack[0].m_obj;
lean_object* v_x_736_ = stack[1].m_obj;
uint8_t v_res_742_;
v_res_742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_735_, v_x_736_);
stack->m_num = v_res_742_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg___boxed(lean_object* v_a_743_, lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_743_, v_x_744_);
lean_dec(v_x_744_);
lean_dec(v_a_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
return v_x_747_;
}
else
{
lean_object* v_key_749_; lean_object* v_value_750_; lean_object* v_tail_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_774_; 
v_key_749_ = lean_ctor_get(v_x_748_, 0);
v_value_750_ = lean_ctor_get(v_x_748_, 1);
v_tail_751_ = lean_ctor_get(v_x_748_, 2);
v_isSharedCheck_774_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_774_ == 0)
{
v___x_753_ = v_x_748_;
v_isShared_754_ = v_isSharedCheck_774_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_tail_751_);
lean_inc(v_value_750_);
lean_inc(v_key_749_);
lean_dec(v_x_748_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_774_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v___x_758_; uint64_t v_fold_759_; uint64_t v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_755_ = lean_array_get_size(v_x_747_);
v___x_756_ = lean_uint64_of_nat(v_key_749_);
v___x_757_ = 32ULL;
v___x_758_ = lean_uint64_shift_right(v___x_756_, v___x_757_);
v_fold_759_ = lean_uint64_xor(v___x_756_, v___x_758_);
v___x_760_ = 16ULL;
v___x_761_ = lean_uint64_shift_right(v_fold_759_, v___x_760_);
v___x_762_ = lean_uint64_xor(v_fold_759_, v___x_761_);
v___x_763_ = lean_uint64_to_usize(v___x_762_);
v___x_764_ = lean_usize_of_nat(v___x_755_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_sub(v___x_764_, v___x_765_);
v___x_767_ = lean_usize_land(v___x_763_, v___x_766_);
v___x_768_ = lean_array_uget_borrowed(v_x_747_, v___x_767_);
lean_inc(v___x_768_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 2, v___x_768_);
v___x_770_ = v___x_753_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_key_749_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_value_750_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v___x_768_);
v___x_770_ = v_reuseFailAlloc_773_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; 
v___x_771_ = lean_array_uset(v_x_747_, v___x_767_, v___x_770_);
v_x_747_ = v___x_771_;
v_x_748_ = v_tail_751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(lean_object* v_i_775_, lean_object* v_source_776_, lean_object* v_target_777_){
_start:
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = lean_array_get_size(v_source_776_);
v___x_779_ = lean_nat_dec_lt(v_i_775_, v___x_778_);
if (v___x_779_ == 0)
{
lean_dec_ref(v_source_776_);
lean_dec(v_i_775_);
return v_target_777_;
}
else
{
lean_object* v_es_780_; lean_object* v___x_781_; lean_object* v_source_782_; lean_object* v_target_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_es_780_ = lean_array_fget(v_source_776_, v_i_775_);
v___x_781_ = lean_box(0);
v_source_782_ = lean_array_fset(v_source_776_, v_i_775_, v___x_781_);
v_target_783_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_target_777_, v_es_780_);
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_i_775_, v___x_784_);
lean_dec(v_i_775_);
v_i_775_ = v___x_785_;
v_source_776_ = v_source_782_;
v_target_777_ = v_target_783_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(lean_object* v_data_787_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_nbuckets_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_788_ = lean_array_get_size(v_data_787_);
v___x_789_ = lean_unsigned_to_nat(2u);
v_nbuckets_790_ = lean_nat_mul(v___x_788_, v___x_789_);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_box(0);
v___x_793_ = lean_mk_array(v_nbuckets_790_, v___x_792_);
v___x_794_ = lean_array_propagate_mark(v_data_787_, v___x_793_);
v___x_795_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v___x_791_, v_data_787_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(lean_object* v_overlapping_796_, lean_object* v_m_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_size_799_; lean_object* v_buckets_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_852_; 
v_size_799_ = lean_ctor_get(v_m_797_, 0);
v_buckets_800_ = lean_ctor_get(v_m_797_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_m_797_);
if (v_isSharedCheck_852_ == 0)
{
v___x_802_ = v_m_797_;
v_isShared_803_ = v_isSharedCheck_852_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_buckets_800_);
lean_inc(v_size_799_);
lean_dec(v_m_797_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_852_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v_fold_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; lean_object* v_bkt_817_; lean_object* v___y_819_; uint8_t v___x_837_; 
v___x_804_ = lean_array_get_size(v_buckets_800_);
v___x_805_ = lean_uint64_of_nat(v_a_798_);
v___x_806_ = 32ULL;
v___x_807_ = lean_uint64_shift_right(v___x_805_, v___x_806_);
v_fold_808_ = lean_uint64_xor(v___x_805_, v___x_807_);
v___x_809_ = 16ULL;
v___x_810_ = lean_uint64_shift_right(v_fold_808_, v___x_809_);
v___x_811_ = lean_uint64_xor(v_fold_808_, v___x_810_);
v___x_812_ = lean_uint64_to_usize(v___x_811_);
v___x_813_ = lean_usize_of_nat(v___x_804_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_sub(v___x_813_, v___x_814_);
v___x_816_ = lean_usize_land(v___x_812_, v___x_815_);
v_bkt_817_ = lean_array_uget_borrowed(v_buckets_800_, v___x_816_);
v___x_837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_798_, v_bkt_817_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_box(1);
v___x_839_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_overlapping_796_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_box(0);
v___x_841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_overlapping_796_, v___x_840_, v___x_838_);
v___y_819_ = v___x_841_;
goto v___jp_818_;
}
else
{
lean_dec(v_overlapping_796_);
v___y_819_ = v___x_838_;
goto v___jp_818_;
}
}
else
{
lean_object* v___x_842_; lean_object* v_buckets_x27_843_; lean_object* v_bkt_x27_844_; lean_object* v___y_846_; uint8_t v___x_849_; 
lean_inc(v_bkt_817_);
lean_del_object(v___x_802_);
v___x_842_ = lean_box(0);
v_buckets_x27_843_ = lean_array_uset(v_buckets_800_, v___x_816_, v___x_842_);
lean_inc(v_a_798_);
v_bkt_x27_844_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__4(v_overlapping_796_, v_a_798_, v_bkt_817_);
v___x_849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_798_, v_bkt_x27_844_);
lean_dec(v_a_798_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_sub(v_size_799_, v___x_850_);
lean_dec(v_size_799_);
v___y_846_ = v___x_851_;
goto v___jp_845_;
}
else
{
v___y_846_ = v_size_799_;
goto v___jp_845_;
}
v___jp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_array_uset(v_buckets_x27_843_, v___x_816_, v_bkt_x27_844_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___y_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
return v___x_848_;
}
}
v___jp_818_:
{
lean_object* v___x_820_; lean_object* v_size_x27_821_; lean_object* v___x_822_; lean_object* v_buckets_x27_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_820_ = lean_unsigned_to_nat(1u);
v_size_x27_821_ = lean_nat_add(v_size_799_, v___x_820_);
lean_dec(v_size_799_);
lean_inc(v_bkt_817_);
v___x_822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_822_, 0, v_a_798_);
lean_ctor_set(v___x_822_, 1, v___y_819_);
lean_ctor_set(v___x_822_, 2, v_bkt_817_);
v_buckets_x27_823_ = lean_array_uset(v_buckets_800_, v___x_816_, v___x_822_);
v___x_824_ = lean_unsigned_to_nat(4u);
v___x_825_ = lean_nat_mul(v_size_x27_821_, v___x_824_);
v___x_826_ = lean_unsigned_to_nat(3u);
v___x_827_ = lean_nat_div(v___x_825_, v___x_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_array_get_size(v_buckets_x27_823_);
v___x_829_ = lean_nat_dec_le(v___x_827_, v___x_828_);
lean_dec(v___x_827_);
if (v___x_829_ == 0)
{
lean_object* v_val_830_; lean_object* v___x_832_; 
v_val_830_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_buckets_x27_823_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v_val_830_);
lean_ctor_set(v___x_802_, 0, v_size_x27_821_);
v___x_832_ = v___x_802_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_size_x27_821_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_val_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
lean_object* v___x_835_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v_buckets_x27_823_);
lean_ctor_set(v___x_802_, 0, v_size_x27_821_);
v___x_835_ = v___x_802_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_size_x27_821_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_buckets_x27_823_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_insert(lean_object* v_o_853_, lean_object* v_overlapping_854_, lean_object* v_overlapped_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2(v_overlapping_854_, v_o_853_, v_overlapped_855_);
return v___x_856_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_object* v_00_u03b2_857_, lean_object* v_k_858_, lean_object* v_t_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___redArg(v_k_858_, v_t_859_);
return v___x_860_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_858_ = stack[1].m_obj;
lean_object* v_t_859_ = stack[2].m_obj;
uint8_t v_res_861_;
v_res_861_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(lean_box(0), v_k_858_, v_t_859_);
stack->m_num = v_res_861_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0___boxed(lean_object* v_00_u03b2_862_, lean_object* v_k_863_, lean_object* v_t_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Match_Overlaps_insert_spec__0(v_00_u03b2_862_, v_k_863_, v_t_864_);
lean_dec(v_t_864_);
lean_dec(v_k_863_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1(lean_object* v_00_u03b2_867_, lean_object* v_k_868_, lean_object* v_v_869_, lean_object* v_t_870_, lean_object* v_hl_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Match_Overlaps_insert_spec__1___redArg(v_k_868_, v_v_869_, v_t_870_);
return v___x_872_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_object* v_00_u03b2_873_, lean_object* v_a_874_, lean_object* v_x_875_){
_start:
{
uint8_t v___x_876_; 
v___x_876_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___redArg(v_a_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_874_ = stack[1].m_obj;
lean_object* v_x_875_ = stack[2].m_obj;
uint8_t v_res_877_;
v_res_877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(lean_box(0), v_a_874_, v_x_875_);
stack->m_num = v_res_877_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2___boxed(lean_object* v_00_u03b2_878_, lean_object* v_a_879_, lean_object* v_x_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__2(v_00_u03b2_878_, v_a_879_, v_x_880_);
lean_dec(v_x_880_);
lean_dec(v_a_879_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3(lean_object* v_00_u03b2_883_, lean_object* v_data_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3___redArg(v_data_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_886_, lean_object* v_i_887_, lean_object* v_source_888_, lean_object* v_target_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4___redArg(v_i_887_, v_source_888_, v_target_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Meta_Match_Overlaps_insert_spec__2_spec__3_spec__4_spec__5___redArg(v_x_892_, v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(lean_object* v_a_895_, lean_object* v_x_896_){
_start:
{
if (lean_obj_tag(v_x_896_) == 0)
{
lean_object* v___x_897_; 
v___x_897_ = lean_box(0);
return v___x_897_;
}
else
{
lean_object* v_key_898_; lean_object* v_value_899_; lean_object* v_tail_900_; uint8_t v___x_901_; 
v_key_898_ = lean_ctor_get(v_x_896_, 0);
v_value_899_ = lean_ctor_get(v_x_896_, 1);
v_tail_900_ = lean_ctor_get(v_x_896_, 2);
v___x_901_ = lean_nat_dec_eq(v_key_898_, v_a_895_);
if (v___x_901_ == 0)
{
v_x_896_ = v_tail_900_;
goto _start;
}
else
{
lean_object* v___x_903_; 
lean_inc(v_value_899_);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v_value_899_);
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg___boxed(lean_object* v_a_904_, lean_object* v_x_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_904_, v_x_905_);
lean_dec(v_x_905_);
lean_dec(v_a_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_buckets_909_; lean_object* v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v_fold_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_buckets_909_ = lean_ctor_get(v_m_907_, 1);
v___x_910_ = lean_array_get_size(v_buckets_909_);
v___x_911_ = lean_uint64_of_nat(v_a_908_);
v___x_912_ = 32ULL;
v___x_913_ = lean_uint64_shift_right(v___x_911_, v___x_912_);
v_fold_914_ = lean_uint64_xor(v___x_911_, v___x_913_);
v___x_915_ = 16ULL;
v___x_916_ = lean_uint64_shift_right(v_fold_914_, v___x_915_);
v___x_917_ = lean_uint64_xor(v_fold_914_, v___x_916_);
v___x_918_ = lean_uint64_to_usize(v___x_917_);
v___x_919_ = lean_usize_of_nat(v___x_910_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_sub(v___x_919_, v___x_920_);
v___x_922_ = lean_usize_land(v___x_918_, v___x_921_);
v___x_923_ = lean_array_uget_borrowed(v_buckets_909_, v___x_922_);
v___x_924_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_908_, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg___boxed(lean_object* v_m_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_m_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(lean_object* v_init_928_, lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_929_) == 0)
{
lean_object* v_k_930_; lean_object* v_l_931_; lean_object* v_r_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_k_930_ = lean_ctor_get(v_x_929_, 1);
lean_inc(v_k_930_);
v_l_931_ = lean_ctor_get(v_x_929_, 3);
lean_inc(v_l_931_);
v_r_932_ = lean_ctor_get(v_x_929_, 4);
lean_inc(v_r_932_);
lean_dec_ref_known(v_x_929_, 5);
v___x_933_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_928_, v_l_931_);
v___x_934_ = lean_array_push(v___x_933_, v_k_930_);
v_init_928_ = v___x_934_;
v_x_929_ = v_r_932_;
goto _start;
}
else
{
return v_init_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object* v_o_938_, lean_object* v_overlapped_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_o_938_, v_overlapped_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = ((lean_object*)(l_Lean_Meta_Match_Overlaps_overlapping___closed__0));
return v___x_941_;
}
else
{
lean_object* v_val_942_; lean_object* v___y_944_; 
v_val_942_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_val_942_);
lean_dec_ref_known(v___x_940_, 1);
if (lean_obj_tag(v_val_942_) == 0)
{
lean_object* v_size_947_; 
v_size_947_ = lean_ctor_get(v_val_942_, 0);
lean_inc(v_size_947_);
v___y_944_ = v_size_947_;
goto v___jp_943_;
}
else
{
lean_object* v___x_948_; 
v___x_948_ = lean_unsigned_to_nat(0u);
v___y_944_ = v___x_948_;
goto v___jp_943_;
}
v___jp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_mk_empty_array_with_capacity(v___y_944_);
lean_dec(v___y_944_);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v___x_945_, v_val_942_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Overlaps_overlapping___boxed(lean_object* v_o_949_, lean_object* v_overlapped_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_Match_Overlaps_overlapping(v_o_949_, v_overlapped_950_);
lean_dec(v_overlapped_950_);
lean_dec_ref(v_o_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(lean_object* v_00_u03b2_952_, lean_object* v_m_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___redArg(v_m_953_, v_a_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0___boxed(lean_object* v_00_u03b2_956_, lean_object* v_m_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0(v_00_u03b2_956_, v_m_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_m_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1(lean_object* v_init_960_, lean_object* v_t_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Match_Overlaps_overlapping_spec__1_spec__2(v_init_960_, v_t_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(lean_object* v_00_u03b2_963_, lean_object* v_a_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___redArg(v_a_964_, v_x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0___boxed(lean_object* v_00_u03b2_967_, lean_object* v_a_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Match_Overlaps_overlapping_spec__0_spec__0(v_00_u03b2_967_, v_a_968_, v_x_969_);
lean_dec(v_x_969_);
lean_dec(v_a_968_);
return v_res_970_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_unsigned_to_nat(13u);
v___x_986_ = lean_nat_to_int(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(15u);
v___x_991_ = lean_nat_to_int(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_unsigned_to_nat(16u);
v___x_996_ = lean_nat_to_int(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(lean_object* v_x_997_){
_start:
{
lean_object* v_numFields_998_; lean_object* v_numOverlaps_999_; uint8_t v_hasUnitThunk_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_numFields_998_ = lean_ctor_get(v_x_997_, 0);
lean_inc(v_numFields_998_);
v_numOverlaps_999_ = lean_ctor_get(v_x_997_, 1);
lean_inc(v_numOverlaps_999_);
v_hasUnitThunk_1000_ = lean_ctor_get_uint8(v_x_997_, sizeof(void*)*2);
lean_dec_ref(v_x_997_);
v___x_1001_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_1002_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__3));
v___x_1003_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_1004_ = l_Nat_reprFast(v_numFields_998_);
v___x_1005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1003_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = 0;
v___x_1008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1002_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_box(1);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__6));
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1001_);
v___x_1017_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__7);
v___x_1018_ = l_Nat_reprFast(v_numOverlaps_999_);
v___x_1019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1017_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set_uint8(v___x_1021_, sizeof(void*)*1, v___x_1007_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1016_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1010_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_1012_);
v___x_1025_ = ((lean_object*)(l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__9));
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1001_);
v___x_1028_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__10);
v___x_1029_ = l_Bool_repr___redArg(v_hasUnitThunk_1000_);
v___x_1030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*1, v___x_1007_);
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1027_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1034_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1032_);
v___x_1036_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1033_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set_uint8(v___x_1039_, sizeof(void*)*1, v___x_1007_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr(lean_object* v_x_1040_, lean_object* v_prec_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_x_1040_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprAltParamInfo_repr___boxed(lean_object* v_x_1043_, lean_object* v_prec_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Meta_Match_instReprAltParamInfo_repr(v_x_1043_, v_prec_1044_);
lean_dec(v_prec_1044_);
return v_res_1045_;
}
}
uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v_numFields_1050_; lean_object* v_numOverlaps_1051_; uint8_t v_hasUnitThunk_1052_; lean_object* v_numFields_1053_; lean_object* v_numOverlaps_1054_; uint8_t v_hasUnitThunk_1055_; uint8_t v___x_1056_; 
v_numFields_1050_ = lean_ctor_get(v_x_1048_, 0);
v_numOverlaps_1051_ = lean_ctor_get(v_x_1048_, 1);
v_hasUnitThunk_1052_ = lean_ctor_get_uint8(v_x_1048_, sizeof(void*)*2);
v_numFields_1053_ = lean_ctor_get(v_x_1049_, 0);
v_numOverlaps_1054_ = lean_ctor_get(v_x_1049_, 1);
v_hasUnitThunk_1055_ = lean_ctor_get_uint8(v_x_1049_, sizeof(void*)*2);
v___x_1056_ = lean_nat_dec_eq(v_numFields_1050_, v_numFields_1053_);
if (v___x_1056_ == 0)
{
return v___x_1056_;
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_nat_dec_eq(v_numOverlaps_1051_, v_numOverlaps_1054_);
if (v___x_1057_ == 0)
{
return v___x_1057_;
}
else
{
if (v_hasUnitThunk_1055_ == 0)
{
if (v_hasUnitThunk_1052_ == 0)
{
return v___x_1057_;
}
else
{
return v_hasUnitThunk_1055_;
}
}
else
{
return v_hasUnitThunk_1052_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_instBEqAltParamInfo_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1048_ = stack[0].m_obj;
lean_object* v_x_1049_ = stack[1].m_obj;
uint8_t v_res_1058_;
v_res_1058_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v_x_1048_, v_x_1049_);
stack->m_num = v_res_1058_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instBEqAltParamInfo_beq___boxed(lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v_x_1059_, v_x_1060_);
lean_dec_ref(v_x_1060_);
lean_dec_ref(v_x_1059_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1067_ = l_Lean_Meta_Match_instInhabitedOverlaps_default;
v___x_1068_ = lean_box(0);
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__0));
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
lean_ctor_set(v___x_1071_, 2, v___x_1069_);
lean_ctor_set(v___x_1071_, 3, v___x_1068_);
lean_ctor_set(v___x_1071_, 4, v___x_1069_);
lean_ctor_set(v___x_1071_, 5, v___x_1067_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_obj_once(&l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1, &l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1_once, _init_l_Lean_Meta_Match_instInhabitedMatcherInfo_default___closed__1);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instInhabitedMatcherInfo(void){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_Match_instInhabitedMatcherInfo_default;
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__1));
return v___x_1076_;
}
else
{
lean_object* v_val_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1088_; 
v_val_1077_ = lean_ctor_get(v_x_1074_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_x_1074_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1079_ = v_x_1074_;
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_val_1077_);
lean_dec(v_x_1074_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1081_ = ((lean_object*)(l_Option_repr___at___00Lean_Meta_Match_instReprDiscrInfo_repr_spec__0___closed__3));
v___x_1082_ = l_Nat_reprFast(v_val_1077_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 3);
lean_ctor_set(v___x_1079_, 0, v___x_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1081_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Repr_addAppParen(v___x_1085_, v_x_1075_);
return v___x_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1___boxed(lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_x_1089_, v_x_1090_);
lean_dec(v_x_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 0)
{
lean_dec(v_x_1092_);
return v_x_1093_;
}
else
{
lean_object* v_head_1095_; lean_object* v_tail_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1106_; 
v_head_1095_ = lean_ctor_get(v_x_1094_, 0);
v_tail_1096_ = lean_ctor_get(v_x_1094_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_x_1094_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1098_ = v_x_1094_;
v_isShared_1099_ = v_isSharedCheck_1106_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_tail_1096_);
lean_inc(v_head_1095_);
lean_dec(v_x_1094_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1106_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
lean_inc(v_x_1092_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 5);
lean_ctor_set(v___x_1098_, 1, v_x_1092_);
lean_ctor_set(v___x_1098_, 0, v_x_1093_);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_x_1093_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_x_1092_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1095_);
v___x_1103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v_x_1093_ = v___x_1103_;
v_x_1094_ = v_tail_1096_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_dec(v_x_1107_);
return v_x_1108_;
}
else
{
lean_object* v_head_1110_; lean_object* v_tail_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1121_; 
v_head_1110_ = lean_ctor_get(v_x_1109_, 0);
v_tail_1111_ = lean_ctor_get(v_x_1109_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1113_ = v_x_1109_;
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_tail_1111_);
lean_inc(v_head_1110_);
lean_dec(v_x_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1121_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
lean_inc(v_x_1107_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 5);
lean_ctor_set(v___x_1113_, 1, v_x_1107_);
lean_ctor_set(v___x_1113_, 0, v_x_1108_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_x_1108_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_x_1107_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1110_);
v___x_1118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_1107_, v___x_1118_, v_tail_1111_);
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_object* v___x_1124_; 
lean_dec(v_x_1123_);
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
else
{
lean_object* v_tail_1125_; 
v_tail_1125_ = lean_ctor_get(v_x_1122_, 1);
if (lean_obj_tag(v_tail_1125_) == 0)
{
lean_object* v_head_1126_; lean_object* v___x_1127_; 
lean_dec(v_x_1123_);
v_head_1126_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_head_1126_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1127_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1126_);
return v___x_1127_;
}
else
{
lean_object* v_head_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_inc(v_tail_1125_);
v_head_1128_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_head_1128_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1129_ = l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg(v_head_1128_);
v___x_1130_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0_spec__2(v_x_1123_, v___x_1129_, v_tail_1125_);
return v___x_1130_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__0));
v___x_1133_ = lean_string_length(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__1);
v___x_1135_ = lean_nat_to_int(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(lean_object* v_xs_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = lean_array_get_size(v_xs_1141_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_nat_dec_eq(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1145_ = lean_array_to_list(v_xs_1141_);
v___x_1146_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_1147_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0_spec__0(v___x_1145_, v___x_1146_);
v___x_1148_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1149_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___x_1147_);
v___x_1151_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_1152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1148_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Std_Format_fill(v___x_1153_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref(v_xs_1141_);
v___x_1155_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(lean_object* v_x_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
if (lean_obj_tag(v_x_1158_) == 0)
{
lean_dec(v_x_1156_);
return v_x_1157_;
}
else
{
lean_object* v_head_1159_; lean_object* v_tail_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1170_; 
v_head_1159_ = lean_ctor_get(v_x_1158_, 0);
v_tail_1160_ = lean_ctor_get(v_x_1158_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_x_1158_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1162_ = v_x_1158_;
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_tail_1160_);
lean_inc(v_head_1159_);
lean_dec(v_x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1170_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
lean_inc(v_x_1156_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set_tag(v___x_1162_, 5);
lean_ctor_set(v___x_1162_, 1, v_x_1156_);
lean_ctor_set(v___x_1162_, 0, v_x_1157_);
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_x_1157_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_x_1156_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1159_);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v_x_1157_ = v___x_1167_;
v_x_1158_ = v_tail_1160_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1173_) == 0)
{
lean_dec(v_x_1171_);
return v_x_1172_;
}
else
{
lean_object* v_head_1174_; lean_object* v_tail_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1185_; 
v_head_1174_ = lean_ctor_get(v_x_1173_, 0);
v_tail_1175_ = lean_ctor_get(v_x_1173_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1177_ = v_x_1173_;
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_tail_1175_);
lean_inc(v_head_1174_);
lean_dec(v_x_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1185_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
lean_inc(v_x_1171_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 5);
lean_ctor_set(v___x_1177_, 1, v_x_1171_);
lean_ctor_set(v___x_1177_, 0, v_x_1172_);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_x_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_x_1171_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1174_);
v___x_1182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5_spec__7(v_x_1171_, v___x_1182_, v_tail_1175_);
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(lean_object* v_x_1186_, lean_object* v_x_1187_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v___x_1188_; 
lean_dec(v_x_1187_);
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
else
{
lean_object* v_tail_1189_; 
v_tail_1189_ = lean_ctor_get(v_x_1186_, 1);
if (lean_obj_tag(v_tail_1189_) == 0)
{
lean_object* v_head_1190_; lean_object* v___x_1191_; 
lean_dec(v_x_1187_);
v_head_1190_ = lean_ctor_get(v_x_1186_, 0);
lean_inc(v_head_1190_);
lean_dec_ref_known(v_x_1186_, 2);
v___x_1191_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1190_);
return v___x_1191_;
}
else
{
lean_object* v_head_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_inc(v_tail_1189_);
v_head_1192_ = lean_ctor_get(v_x_1186_, 0);
lean_inc(v_head_1192_);
lean_dec_ref_known(v_x_1186_, 2);
v___x_1193_ = l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg(v_head_1192_);
v___x_1194_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3_spec__5(v_x_1187_, v___x_1193_, v_tail_1189_);
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(lean_object* v_xs_1195_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1196_ = lean_array_get_size(v_xs_1195_);
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_nat_dec_eq(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1199_ = lean_array_to_list(v_xs_1195_);
v___x_1200_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__5));
v___x_1201_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2_spec__3(v___x_1199_, v___x_1200_);
v___x_1202_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2, &l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__2);
v___x_1203_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__3));
v___x_1204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
lean_ctor_set(v___x_1204_, 1, v___x_1201_);
v___x_1205_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__10));
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1202_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = l_Std_Format_fill(v___x_1207_);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; 
lean_dec_ref(v_xs_1195_);
v___x_1209_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0___closed__5));
return v___x_1209_;
}
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(12u);
v___x_1226_ = lean_nat_to_int(v___x_1225_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(14u);
v___x_1234_ = lean_nat_to_int(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(lean_object* v_x_1238_){
_start:
{
lean_object* v_numParams_1239_; lean_object* v_numDiscrs_1240_; lean_object* v_altInfos_1241_; lean_object* v_uElimPos_x3f_1242_; lean_object* v_discrInfos_1243_; lean_object* v_overlaps_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_numParams_1239_ = lean_ctor_get(v_x_1238_, 0);
lean_inc(v_numParams_1239_);
v_numDiscrs_1240_ = lean_ctor_get(v_x_1238_, 1);
lean_inc(v_numDiscrs_1240_);
v_altInfos_1241_ = lean_ctor_get(v_x_1238_, 2);
lean_inc_ref(v_altInfos_1241_);
v_uElimPos_x3f_1242_ = lean_ctor_get(v_x_1238_, 3);
lean_inc(v_uElimPos_x3f_1242_);
v_discrInfos_1243_ = lean_ctor_get(v_x_1238_, 4);
lean_inc_ref(v_discrInfos_1243_);
v_overlaps_1244_ = lean_ctor_get(v_x_1238_, 5);
lean_inc_ref(v_overlaps_1244_);
lean_dec_ref(v_x_1238_);
v___x_1245_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__5));
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__3));
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4, &l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4_once, _init_l_Lean_Meta_Match_instReprAltParamInfo_repr___redArg___closed__4);
v___x_1248_ = l_Nat_reprFast(v_numParams_1239_);
v___x_1249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1247_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = 0;
v___x_1252_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1246_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = ((lean_object*)(l_List_repr___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Match_instReprOverlaps_repr_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_1255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_box(1);
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__5));
v___x_1259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1245_);
v___x_1261_ = l_Nat_reprFast(v_numDiscrs_1240_);
v___x_1262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1247_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*1, v___x_1251_);
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1260_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1254_);
v___x_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1256_);
v___x_1268_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__7));
v___x_1269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___x_1245_);
v___x_1271_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__8);
v___x_1272_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__0(v_altInfos_1241_);
v___x_1273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*1, v___x_1251_);
v___x_1275_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1270_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v___x_1254_);
v___x_1277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___x_1256_);
v___x_1278_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__10));
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v___x_1245_);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = l_Option_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__1(v_uElimPos_x3f_1242_, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1247_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1251_);
v___x_1285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1280_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___x_1254_);
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set(v___x_1287_, 1, v___x_1256_);
v___x_1288_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__12));
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1245_);
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13, &l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13_once, _init_l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__13);
v___x_1292_ = l_Array_repr___at___00Lean_Meta_Match_instReprMatcherInfo_repr_spec__2(v_discrInfos_1243_);
v___x_1293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*1, v___x_1251_);
v___x_1295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1290_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1254_);
v___x_1297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v___x_1256_);
v___x_1298_ = ((lean_object*)(l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg___closed__15));
v___x_1299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1297_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1245_);
v___x_1301_ = l_Lean_Meta_Match_instReprOverlaps_repr___redArg(v_overlaps_1244_);
v___x_1302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1271_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*1, v___x_1251_);
v___x_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1300_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10, &l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10_once, _init_l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__10);
v___x_1306_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__11));
v___x_1307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1304_);
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Match_instReprDiscrInfo_repr___redArg___closed__12));
v___x_1309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1305_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*1, v___x_1251_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr(lean_object* v_x_1312_, lean_object* v_prec_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Meta_Match_instReprMatcherInfo_repr___redArg(v_x_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_instReprMatcherInfo_repr___boxed(lean_object* v_x_1315_, lean_object* v_prec_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Match_instReprMatcherInfo_repr(v_x_1315_, v_prec_1316_);
lean_dec(v_prec_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object* v_info_1320_){
_start:
{
lean_object* v_altInfos_1321_; lean_object* v___x_1322_; 
v_altInfos_1321_ = lean_ctor_get(v_info_1320_, 2);
v___x_1322_ = lean_array_get_size(v_altInfos_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts___boxed(lean_object* v_info_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1323_);
lean_dec_ref(v_info_1323_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object* v_info_1325_){
_start:
{
lean_object* v_numParams_1326_; lean_object* v_numDiscrs_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_numParams_1326_ = lean_ctor_get(v_info_1325_, 0);
v_numDiscrs_1327_ = lean_ctor_get(v_info_1325_, 1);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v_numParams_1326_, v___x_1328_);
v___x_1330_ = lean_nat_add(v___x_1329_, v_numDiscrs_1327_);
lean_dec(v___x_1329_);
v___x_1331_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1325_);
v___x_1332_ = lean_nat_add(v___x_1330_, v___x_1331_);
lean_dec(v___x_1331_);
lean_dec(v___x_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_arity___boxed(lean_object* v_info_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Meta_Match_MatcherInfo_arity(v_info_1333_);
lean_dec_ref(v_info_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object* v_info_1335_){
_start:
{
lean_object* v_numParams_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_numParams_1336_ = lean_ctor_get(v_info_1335_, 0);
v___x_1337_ = lean_unsigned_to_nat(1u);
v___x_1338_ = lean_nat_add(v_numParams_1336_, v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos___boxed(lean_object* v_info_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1339_);
lean_dec_ref(v_info_1339_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange(lean_object* v_info_1341_){
_start:
{
lean_object* v_numDiscrs_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_numDiscrs_1342_ = lean_ctor_get(v_info_1341_, 1);
v___x_1343_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_info_1341_);
v___x_1344_ = lean_nat_add(v___x_1343_, v_numDiscrs_1342_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getDiscrRange___boxed(lean_object* v_info_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Meta_Match_MatcherInfo_getDiscrRange(v_info_1346_);
lean_dec_ref(v_info_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object* v_info_1348_){
_start:
{
lean_object* v_numParams_1349_; lean_object* v_numDiscrs_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_numParams_1349_ = lean_ctor_get(v_info_1348_, 0);
v_numDiscrs_1350_ = lean_ctor_get(v_info_1348_, 1);
v___x_1351_ = lean_unsigned_to_nat(1u);
v___x_1352_ = lean_nat_add(v_numParams_1349_, v___x_1351_);
v___x_1353_ = lean_nat_add(v___x_1352_, v_numDiscrs_1350_);
lean_dec(v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos___boxed(lean_object* v_info_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1354_);
lean_dec_ref(v_info_1354_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange(lean_object* v_info_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(v_info_1356_);
v___x_1358_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_info_1356_);
v___x_1359_ = lean_nat_add(v___x_1357_, v___x_1358_);
lean_dec(v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1357_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getAltRange___boxed(lean_object* v_info_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Meta_Match_MatcherInfo_getAltRange(v_info_1361_);
lean_dec_ref(v_info_1361_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object* v_info_1363_){
_start:
{
lean_object* v_numParams_1364_; 
v_numParams_1364_ = lean_ctor_get(v_info_1363_, 0);
lean_inc(v_numParams_1364_);
return v_numParams_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos___boxed(lean_object* v_info_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_info_1365_);
lean_dec_ref(v_info_1365_);
return v_res_1366_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(lean_object* v_as_1367_, size_t v_sz_1368_, size_t v_i_1369_, lean_object* v_b_1370_){
_start:
{
lean_object* v_a_1372_; uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1369_, v_sz_1368_);
if (v___x_1376_ == 0)
{
return v_b_1370_;
}
else
{
lean_object* v_a_1377_; 
v_a_1377_ = lean_array_uget_borrowed(v_as_1367_, v_i_1369_);
if (lean_obj_tag(v_a_1377_) == 0)
{
v_a_1372_ = v_b_1370_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_add(v_b_1370_, v___x_1378_);
lean_dec(v_b_1370_);
v_a_1372_ = v___x_1379_;
goto v___jp_1371_;
}
}
v___jp_1371_:
{
size_t v___x_1373_; size_t v___x_1374_; 
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_add(v_i_1369_, v___x_1373_);
v_i_1369_ = v___x_1374_;
v_b_1370_ = v_a_1372_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1367_ = stack[0].m_obj;
size_t v_sz_1368_ = stack[1].m_num;
size_t v_i_1369_ = stack[2].m_num;
lean_object* v_b_1370_ = stack[3].m_obj;
lean_object* v_res_1380_;
v_res_1380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_as_1367_, v_sz_1368_, v_i_1369_, v_b_1370_);
stack->m_obj
 = v_res_1380_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0___boxed(lean_object* v_as_1381_, lean_object* v_sz_1382_, lean_object* v_i_1383_, lean_object* v_b_1384_){
_start:
{
size_t v_sz_boxed_1385_; size_t v_i_boxed_1386_; lean_object* v_res_1387_; 
v_sz_boxed_1385_ = lean_unbox_usize(v_sz_1382_);
lean_dec(v_sz_1382_);
v_i_boxed_1386_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_as_1381_, v_sz_boxed_1385_, v_i_boxed_1386_, v_b_1384_);
lean_dec_ref(v_as_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos(lean_object* v_infos_1388_){
_start:
{
lean_object* v_r_1389_; size_t v_sz_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
v_r_1389_ = lean_unsigned_to_nat(0u);
v_sz_1390_ = lean_array_size(v_infos_1388_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Match_getNumEqsFromDiscrInfos_spec__0(v_infos_1388_, v_sz_1390_, v___x_1391_, v_r_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos___boxed(lean_object* v_infos_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_infos_1393_);
lean_dec_ref(v_infos_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object* v_info_1395_){
_start:
{
lean_object* v_discrInfos_1396_; lean_object* v___x_1397_; 
v_discrInfos_1396_ = lean_ctor_get(v_info_1395_, 4);
v___x_1397_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs___boxed(lean_object* v_info_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1398_);
lean_dec_ref(v_info_1398_);
return v_res_1399_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(lean_object* v_info_1400_, size_t v_sz_1401_, size_t v_i_1402_, lean_object* v_bs_1403_){
_start:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_usize_dec_lt(v_i_1402_, v_sz_1401_);
if (v___x_1404_ == 0)
{
return v_bs_1403_;
}
else
{
lean_object* v_v_1405_; lean_object* v_numFields_1406_; lean_object* v_numOverlaps_1407_; uint8_t v_hasUnitThunk_1408_; lean_object* v___x_1409_; lean_object* v_bs_x27_1410_; lean_object* v___x_1411_; lean_object* v___y_1413_; 
v_v_1405_ = lean_array_uget_borrowed(v_bs_1403_, v_i_1402_);
v_numFields_1406_ = lean_ctor_get(v_v_1405_, 0);
lean_inc(v_numFields_1406_);
v_numOverlaps_1407_ = lean_ctor_get(v_v_1405_, 1);
lean_inc(v_numOverlaps_1407_);
v_hasUnitThunk_1408_ = lean_ctor_get_uint8(v_v_1405_, sizeof(void*)*2);
v___x_1409_ = lean_unsigned_to_nat(0u);
v_bs_x27_1410_ = lean_array_uset(v_bs_1403_, v_i_1402_, v___x_1409_);
v___x_1411_ = lean_nat_add(v_numFields_1406_, v_numOverlaps_1407_);
lean_dec(v_numOverlaps_1407_);
lean_dec(v_numFields_1406_);
if (v_hasUnitThunk_1408_ == 0)
{
v___y_1413_ = v___x_1409_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_unsigned_to_nat(1u);
v___y_1413_ = v___x_1421_;
goto v___jp_1412_;
}
v___jp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1414_ = lean_nat_add(v___x_1411_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec(v___x_1411_);
v___x_1415_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_info_1400_);
v___x_1416_ = lean_nat_add(v___x_1414_, v___x_1415_);
lean_dec(v___x_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = lean_usize_add(v_i_1402_, v___x_1417_);
v___x_1419_ = lean_array_uset(v_bs_x27_1410_, v_i_1402_, v___x_1416_);
v_i_1402_ = v___x_1418_;
v_bs_1403_ = v___x_1419_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1400_ = stack[0].m_obj;
size_t v_sz_1401_ = stack[1].m_num;
size_t v_i_1402_ = stack[2].m_num;
lean_object* v_bs_1403_ = stack[3].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1400_, v_sz_1401_, v_i_1402_, v_bs_1403_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0___boxed(lean_object* v_info_1423_, lean_object* v_sz_1424_, lean_object* v_i_1425_, lean_object* v_bs_1426_){
_start:
{
size_t v_sz_boxed_1427_; size_t v_i_boxed_1428_; lean_object* v_res_1429_; 
v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1424_);
lean_dec(v_sz_1424_);
v_i_boxed_1428_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1423_, v_sz_boxed_1427_, v_i_boxed_1428_, v_bs_1426_);
lean_dec_ref(v_info_1423_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_MatcherInfo_altNumParams(lean_object* v_info_1430_){
_start:
{
lean_object* v_altInfos_1431_; size_t v_sz_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v_altInfos_1431_ = lean_ctor_get(v_info_1430_, 2);
lean_inc_ref(v_altInfos_1431_);
v_sz_1432_ = lean_array_size(v_altInfos_1431_);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Match_MatcherInfo_altNumParams_spec__0(v_info_1430_, v_sz_1432_, v___x_1433_, v_altInfos_1431_);
lean_dec_ref(v_info_1430_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_unsigned_to_nat(16u);
v___x_1437_ = lean_mk_array(v___x_1436_, v___x_1435_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__0, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__0_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__0);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v___x_1438_);
return v___x_1440_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__2, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__2_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__2);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; 
v___x_1444_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__3, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__3_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__3);
v___x_1445_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__1, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__1_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__1);
v___x_1446_ = 1;
v___x_1447_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1444_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*2, v___x_1446_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_Meta_Match_Extension_instInhabitedState(void){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__4, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4);
return v___x_1448_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_1449_, lean_object* v_x_1450_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = 0;
return v___x_1451_;
}
else
{
lean_object* v_key_1452_; lean_object* v_tail_1453_; uint8_t v___x_1454_; 
v_key_1452_ = lean_ctor_get(v_x_1450_, 0);
v_tail_1453_ = lean_ctor_get(v_x_1450_, 2);
v___x_1454_ = lean_name_eq(v_key_1452_, v_a_1449_);
if (v___x_1454_ == 0)
{
v_x_1450_ = v_tail_1453_;
goto _start;
}
else
{
return v___x_1454_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1449_ = stack[0].m_obj;
lean_object* v_x_1450_ = stack[1].m_obj;
uint8_t v_res_1456_;
v_res_1456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1449_, v_x_1450_);
stack->m_num = v_res_1456_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_1457_, lean_object* v_x_1458_){
_start:
{
uint8_t v_res_1459_; lean_object* v_r_1460_; 
v_res_1459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1457_, v_x_1458_);
lean_dec(v_x_1458_);
lean_dec(v_a_1457_);
v_r_1460_ = lean_box(v_res_1459_);
return v_r_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
return v_x_1461_;
}
else
{
lean_object* v_key_1463_; lean_object* v_value_1464_; lean_object* v_tail_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1491_; 
v_key_1463_ = lean_ctor_get(v_x_1462_, 0);
v_value_1464_ = lean_ctor_get(v_x_1462_, 1);
v_tail_1465_ = lean_ctor_get(v_x_1462_, 2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1467_ = v_x_1462_;
v_isShared_1468_ = v_isSharedCheck_1491_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_tail_1465_);
lean_inc(v_value_1464_);
lean_inc(v_key_1463_);
lean_dec(v_x_1462_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1491_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; uint64_t v___y_1471_; 
v___x_1469_ = lean_array_get_size(v_x_1461_);
if (lean_obj_tag(v_key_1463_) == 0)
{
uint64_t v___x_1489_; 
v___x_1489_ = 1723ULL;
v___y_1471_ = v___x_1489_;
goto v___jp_1470_;
}
else
{
uint64_t v_hash_1490_; 
v_hash_1490_ = lean_ctor_get_uint64(v_key_1463_, sizeof(void*)*2);
v___y_1471_ = v_hash_1490_;
goto v___jp_1470_;
}
v___jp_1470_:
{
uint64_t v___x_1472_; uint64_t v___x_1473_; uint64_t v_fold_1474_; uint64_t v___x_1475_; uint64_t v___x_1476_; uint64_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; size_t v___x_1481_; size_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1472_ = 32ULL;
v___x_1473_ = lean_uint64_shift_right(v___y_1471_, v___x_1472_);
v_fold_1474_ = lean_uint64_xor(v___y_1471_, v___x_1473_);
v___x_1475_ = 16ULL;
v___x_1476_ = lean_uint64_shift_right(v_fold_1474_, v___x_1475_);
v___x_1477_ = lean_uint64_xor(v_fold_1474_, v___x_1476_);
v___x_1478_ = lean_uint64_to_usize(v___x_1477_);
v___x_1479_ = lean_usize_of_nat(v___x_1469_);
v___x_1480_ = ((size_t)1ULL);
v___x_1481_ = lean_usize_sub(v___x_1479_, v___x_1480_);
v___x_1482_ = lean_usize_land(v___x_1478_, v___x_1481_);
v___x_1483_ = lean_array_uget_borrowed(v_x_1461_, v___x_1482_);
lean_inc(v___x_1483_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 2, v___x_1483_);
v___x_1485_ = v___x_1467_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_key_1463_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_value_1464_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_array_uset(v_x_1461_, v___x_1482_, v___x_1485_);
v_x_1461_ = v___x_1486_;
v_x_1462_ = v_tail_1465_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_1492_, lean_object* v_source_1493_, lean_object* v_target_1494_){
_start:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_array_get_size(v_source_1493_);
v___x_1496_ = lean_nat_dec_lt(v_i_1492_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_dec_ref(v_source_1493_);
lean_dec(v_i_1492_);
return v_target_1494_;
}
else
{
lean_object* v_es_1497_; lean_object* v___x_1498_; lean_object* v_source_1499_; lean_object* v_target_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_es_1497_ = lean_array_fget(v_source_1493_, v_i_1492_);
v___x_1498_ = lean_box(0);
v_source_1499_ = lean_array_fset(v_source_1493_, v_i_1492_, v___x_1498_);
v_target_1500_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_1494_, v_es_1497_);
v___x_1501_ = lean_unsigned_to_nat(1u);
v___x_1502_ = lean_nat_add(v_i_1492_, v___x_1501_);
lean_dec(v_i_1492_);
v_i_1492_ = v___x_1502_;
v_source_1493_ = v_source_1499_;
v_target_1494_ = v_target_1500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(lean_object* v_data_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_nbuckets_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1505_ = lean_array_get_size(v_data_1504_);
v___x_1506_ = lean_unsigned_to_nat(2u);
v_nbuckets_1507_ = lean_nat_mul(v___x_1505_, v___x_1506_);
v___x_1508_ = lean_unsigned_to_nat(0u);
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_mk_array(v_nbuckets_1507_, v___x_1509_);
v___x_1511_ = lean_array_propagate_mark(v_data_1504_, v___x_1510_);
v___x_1512_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_1508_, v_data_1504_, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_a_1513_, lean_object* v_b_1514_, lean_object* v_x_1515_){
_start:
{
if (lean_obj_tag(v_x_1515_) == 0)
{
lean_dec(v_b_1514_);
lean_dec(v_a_1513_);
return v_x_1515_;
}
else
{
lean_object* v_key_1516_; lean_object* v_value_1517_; lean_object* v_tail_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1530_; 
v_key_1516_ = lean_ctor_get(v_x_1515_, 0);
v_value_1517_ = lean_ctor_get(v_x_1515_, 1);
v_tail_1518_ = lean_ctor_get(v_x_1515_, 2);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1520_ = v_x_1515_;
v_isShared_1521_ = v_isSharedCheck_1530_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_tail_1518_);
lean_inc(v_value_1517_);
lean_inc(v_key_1516_);
lean_dec(v_x_1515_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1530_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_name_eq(v_key_1516_, v_a_1513_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1513_, v_b_1514_, v_tail_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 2, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_key_1516_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_value_1517_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
else
{
lean_object* v___x_1528_; 
lean_dec(v_value_1517_);
lean_dec(v_key_1516_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v_b_1514_);
lean_ctor_set(v___x_1520_, 0, v_a_1513_);
v___x_1528_ = v___x_1520_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1513_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_b_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_tail_1518_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(lean_object* v_m_1531_, lean_object* v_a_1532_, lean_object* v_b_1533_){
_start:
{
lean_object* v_size_1534_; lean_object* v_buckets_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1581_; 
v_size_1534_ = lean_ctor_get(v_m_1531_, 0);
v_buckets_1535_ = lean_ctor_get(v_m_1531_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_m_1531_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1537_ = v_m_1531_;
v_isShared_1538_ = v_isSharedCheck_1581_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_buckets_1535_);
lean_inc(v_size_1534_);
lean_dec(v_m_1531_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1581_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; uint64_t v___y_1541_; 
v___x_1539_ = lean_array_get_size(v_buckets_1535_);
if (lean_obj_tag(v_a_1532_) == 0)
{
uint64_t v___x_1579_; 
v___x_1579_ = 1723ULL;
v___y_1541_ = v___x_1579_;
goto v___jp_1540_;
}
else
{
uint64_t v_hash_1580_; 
v_hash_1580_ = lean_ctor_get_uint64(v_a_1532_, sizeof(void*)*2);
v___y_1541_ = v_hash_1580_;
goto v___jp_1540_;
}
v___jp_1540_:
{
uint64_t v___x_1542_; uint64_t v___x_1543_; uint64_t v_fold_1544_; uint64_t v___x_1545_; uint64_t v___x_1546_; uint64_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; size_t v___x_1551_; size_t v___x_1552_; lean_object* v_bkt_1553_; uint8_t v___x_1554_; 
v___x_1542_ = 32ULL;
v___x_1543_ = lean_uint64_shift_right(v___y_1541_, v___x_1542_);
v_fold_1544_ = lean_uint64_xor(v___y_1541_, v___x_1543_);
v___x_1545_ = 16ULL;
v___x_1546_ = lean_uint64_shift_right(v_fold_1544_, v___x_1545_);
v___x_1547_ = lean_uint64_xor(v_fold_1544_, v___x_1546_);
v___x_1548_ = lean_uint64_to_usize(v___x_1547_);
v___x_1549_ = lean_usize_of_nat(v___x_1539_);
v___x_1550_ = ((size_t)1ULL);
v___x_1551_ = lean_usize_sub(v___x_1549_, v___x_1550_);
v___x_1552_ = lean_usize_land(v___x_1548_, v___x_1551_);
v_bkt_1553_ = lean_array_uget_borrowed(v_buckets_1535_, v___x_1552_);
v___x_1554_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1532_, v_bkt_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v_size_x27_1556_; lean_object* v___x_1557_; lean_object* v_buckets_x27_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
v_size_x27_1556_ = lean_nat_add(v_size_1534_, v___x_1555_);
lean_dec(v_size_1534_);
lean_inc(v_bkt_1553_);
v___x_1557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1557_, 0, v_a_1532_);
lean_ctor_set(v___x_1557_, 1, v_b_1533_);
lean_ctor_set(v___x_1557_, 2, v_bkt_1553_);
v_buckets_x27_1558_ = lean_array_uset(v_buckets_1535_, v___x_1552_, v___x_1557_);
v___x_1559_ = lean_unsigned_to_nat(4u);
v___x_1560_ = lean_nat_mul(v_size_x27_1556_, v___x_1559_);
v___x_1561_ = lean_unsigned_to_nat(3u);
v___x_1562_ = lean_nat_div(v___x_1560_, v___x_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_array_get_size(v_buckets_x27_1558_);
v___x_1564_ = lean_nat_dec_le(v___x_1562_, v___x_1563_);
lean_dec(v___x_1562_);
if (v___x_1564_ == 0)
{
lean_object* v_val_1565_; lean_object* v___x_1567_; 
v_val_1565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_1558_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v_val_1565_);
lean_ctor_set(v___x_1537_, 0, v_size_x27_1556_);
v___x_1567_ = v___x_1537_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_size_x27_1556_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_val_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
else
{
lean_object* v___x_1570_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v_buckets_x27_1558_);
lean_ctor_set(v___x_1537_, 0, v_size_x27_1556_);
v___x_1570_ = v___x_1537_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_size_x27_1556_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_buckets_x27_1558_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
else
{
lean_object* v___x_1572_; lean_object* v_buckets_x27_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
lean_inc(v_bkt_1553_);
v___x_1572_ = lean_box(0);
v_buckets_x27_1573_ = lean_array_uset(v_buckets_1535_, v___x_1552_, v___x_1572_);
v___x_1574_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1532_, v_b_1533_, v_bkt_1553_);
v___x_1575_ = lean_array_uset(v_buckets_x27_1573_, v___x_1552_, v___x_1574_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v___x_1575_);
v___x_1577_ = v___x_1537_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_size_1534_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_){
_start:
{
lean_object* v_ks_1586_; lean_object* v_vs_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1611_; 
v_ks_1586_ = lean_ctor_get(v_x_1582_, 0);
v_vs_1587_ = lean_ctor_get(v_x_1582_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1582_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1589_ = v_x_1582_;
v_isShared_1590_ = v_isSharedCheck_1611_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_vs_1587_);
lean_inc(v_ks_1586_);
lean_dec(v_x_1582_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1611_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_array_get_size(v_ks_1586_);
v___x_1592_ = lean_nat_dec_lt(v_x_1583_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
lean_dec(v_x_1583_);
v___x_1593_ = lean_array_push(v_ks_1586_, v_x_1584_);
v___x_1594_ = lean_array_push(v_vs_1587_, v_x_1585_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v___x_1594_);
lean_ctor_set(v___x_1589_, 0, v___x_1593_);
v___x_1596_ = v___x_1589_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
else
{
lean_object* v_k_x27_1598_; uint8_t v___x_1599_; 
v_k_x27_1598_ = lean_array_fget_borrowed(v_ks_1586_, v_x_1583_);
v___x_1599_ = lean_name_eq(v_x_1584_, v_k_x27_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1601_; 
if (v_isShared_1590_ == 0)
{
v___x_1601_ = v___x_1589_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_ks_1586_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_vs_1587_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_add(v_x_1583_, v___x_1602_);
lean_dec(v_x_1583_);
v_x_1582_ = v___x_1601_;
v_x_1583_ = v___x_1603_;
goto _start;
}
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = lean_array_fset(v_ks_1586_, v_x_1583_, v_x_1584_);
v___x_1607_ = lean_array_fset(v_vs_1587_, v_x_1583_, v_x_1585_);
lean_dec(v_x_1583_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v___x_1607_);
lean_ctor_set(v___x_1589_, 0, v___x_1606_);
v___x_1609_ = v___x_1589_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_1612_, lean_object* v_k_1613_, lean_object* v_v_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_1612_, v___x_1615_, v_k_1613_, v_v_1614_);
return v___x_1616_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1617_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1618_, size_t v_x_1619_, size_t v_x_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1618_) == 0)
{
lean_object* v_es_1623_; size_t v___x_1624_; size_t v___x_1625_; lean_object* v_j_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v_es_1623_ = lean_ctor_get(v_x_1618_, 0);
v___x_1624_ = ((size_t)31ULL);
v___x_1625_ = lean_usize_land(v_x_1619_, v___x_1624_);
v_j_1626_ = lean_usize_to_nat(v___x_1625_);
v___x_1627_ = lean_array_get_size(v_es_1623_);
v___x_1628_ = lean_nat_dec_lt(v_j_1626_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_dec(v_j_1626_);
lean_dec(v_x_1622_);
lean_dec(v_x_1621_);
return v_x_1618_;
}
else
{
lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1667_; 
lean_inc_ref(v_es_1623_);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_x_1618_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v_x_1618_, 0);
lean_dec(v_unused_1668_);
v___x_1630_ = v_x_1618_;
v_isShared_1631_ = v_isSharedCheck_1667_;
goto v_resetjp_1629_;
}
else
{
lean_dec(v_x_1618_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1667_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_v_1632_; lean_object* v___x_1633_; lean_object* v_xs_x27_1634_; lean_object* v___y_1636_; 
v_v_1632_ = lean_array_fget(v_es_1623_, v_j_1626_);
v___x_1633_ = lean_box(0);
v_xs_x27_1634_ = lean_array_fset(v_es_1623_, v_j_1626_, v___x_1633_);
switch(lean_obj_tag(v_v_1632_))
{
case 0:
{
lean_object* v_key_1641_; lean_object* v_val_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1652_; 
v_key_1641_ = lean_ctor_get(v_v_1632_, 0);
v_val_1642_ = lean_ctor_get(v_v_1632_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_v_1632_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1644_ = v_v_1632_;
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_val_1642_);
lean_inc(v_key_1641_);
lean_dec(v_v_1632_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_name_eq(v_x_1621_, v_key_1641_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_del_object(v___x_1644_);
v___x_1647_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1641_, v_val_1642_, v_x_1621_, v_x_1622_);
v___x_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
v___y_1636_ = v___x_1648_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1650_; 
lean_dec(v_val_1642_);
lean_dec(v_key_1641_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v_x_1622_);
lean_ctor_set(v___x_1644_, 0, v_x_1621_);
v___x_1650_ = v___x_1644_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_x_1621_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_x_1622_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
v___y_1636_ = v___x_1650_;
goto v___jp_1635_;
}
}
}
}
case 1:
{
lean_object* v_node_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1665_; 
v_node_1653_ = lean_ctor_get(v_v_1632_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_v_1632_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1655_ = v_v_1632_;
v_isShared_1656_ = v_isSharedCheck_1665_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_node_1653_);
lean_dec(v_v_1632_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1665_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
size_t v___x_1657_; size_t v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1657_ = ((size_t)5ULL);
v___x_1658_ = lean_usize_shift_right(v_x_1619_, v___x_1657_);
v___x_1659_ = ((size_t)1ULL);
v___x_1660_ = lean_usize_add(v_x_1620_, v___x_1659_);
v___x_1661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_node_1653_, v___x_1658_, v___x_1660_, v_x_1621_, v_x_1622_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1661_);
v___x_1663_ = v___x_1655_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
v___y_1636_ = v___x_1663_;
goto v___jp_1635_;
}
}
}
default: 
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_x_1621_);
lean_ctor_set(v___x_1666_, 1, v_x_1622_);
v___y_1636_ = v___x_1666_;
goto v___jp_1635_;
}
}
v___jp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = lean_array_fset(v_xs_x27_1634_, v_j_1626_, v___y_1636_);
lean_dec(v_j_1626_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1637_);
v___x_1639_ = v___x_1630_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
else
{
lean_object* v_ks_1669_; lean_object* v_vs_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1688_; 
v_ks_1669_ = lean_ctor_get(v_x_1618_, 0);
v_vs_1670_ = lean_ctor_get(v_x_1618_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_x_1618_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1672_ = v_x_1618_;
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_vs_1670_);
lean_inc(v_ks_1669_);
lean_dec(v_x_1618_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1688_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_ks_1669_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_vs_1670_);
v___x_1675_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v_newNode_1676_; size_t v___x_1677_; uint8_t v___x_1678_; 
v_newNode_1676_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1675_, v_x_1621_, v_x_1622_);
v___x_1677_ = ((size_t)7ULL);
v___x_1678_ = lean_usize_dec_le(v___x_1677_, v_x_1620_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1679_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1676_);
v___x_1680_ = lean_unsigned_to_nat(4u);
v___x_1681_ = lean_nat_dec_lt(v___x_1679_, v___x_1680_);
lean_dec(v___x_1679_);
if (v___x_1681_ == 0)
{
lean_object* v_ks_1682_; lean_object* v_vs_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_ks_1682_ = lean_ctor_get(v_newNode_1676_, 0);
lean_inc_ref(v_ks_1682_);
v_vs_1683_ = lean_ctor_get(v_newNode_1676_, 1);
lean_inc_ref(v_vs_1683_);
lean_dec_ref(v_newNode_1676_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_1686_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1620_, v_ks_1682_, v_vs_1683_, v___x_1684_, v___x_1685_);
lean_dec_ref(v_vs_1683_);
lean_dec_ref(v_ks_1682_);
return v___x_1686_;
}
else
{
return v_newNode_1676_;
}
}
else
{
return v_newNode_1676_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1618_ = stack[0].m_obj;
size_t v_x_1619_ = stack[1].m_num;
size_t v_x_1620_ = stack[2].m_num;
lean_object* v_x_1621_ = stack[3].m_obj;
lean_object* v_x_1622_ = stack[4].m_obj;
lean_object* v_res_1689_;
v_res_1689_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1618_, v_x_1619_, v_x_1620_, v_x_1621_, v_x_1622_);
stack->m_obj
 = v_res_1689_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_1690_, lean_object* v_keys_1691_, lean_object* v_vals_1692_, lean_object* v_i_1693_, lean_object* v_entries_1694_){
_start:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = lean_array_get_size(v_keys_1691_);
v___x_1696_ = lean_nat_dec_lt(v_i_1693_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec(v_i_1693_);
return v_entries_1694_;
}
else
{
lean_object* v_k_1697_; lean_object* v_v_1698_; uint64_t v___y_1700_; 
v_k_1697_ = lean_array_fget_borrowed(v_keys_1691_, v_i_1693_);
v_v_1698_ = lean_array_fget_borrowed(v_vals_1692_, v_i_1693_);
if (lean_obj_tag(v_k_1697_) == 0)
{
uint64_t v___x_1711_; 
v___x_1711_ = 1723ULL;
v___y_1700_ = v___x_1711_;
goto v___jp_1699_;
}
else
{
uint64_t v_hash_1712_; 
v_hash_1712_ = lean_ctor_get_uint64(v_k_1697_, sizeof(void*)*2);
v___y_1700_ = v_hash_1712_;
goto v___jp_1699_;
}
v___jp_1699_:
{
size_t v_h_1701_; size_t v___x_1702_; lean_object* v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; size_t v___x_1706_; size_t v_h_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_h_1701_ = lean_uint64_to_usize(v___y_1700_);
v___x_1702_ = ((size_t)5ULL);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_sub(v_depth_1690_, v___x_1704_);
v___x_1706_ = lean_usize_mul(v___x_1702_, v___x_1705_);
v_h_1707_ = lean_usize_shift_right(v_h_1701_, v___x_1706_);
v___x_1708_ = lean_nat_add(v_i_1693_, v___x_1703_);
lean_dec(v_i_1693_);
lean_inc(v_v_1698_);
lean_inc(v_k_1697_);
v___x_1709_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_entries_1694_, v_h_1707_, v_depth_1690_, v_k_1697_, v_v_1698_);
v_i_1693_ = v___x_1708_;
v_entries_1694_ = v___x_1709_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1690_ = stack[0].m_num;
lean_object* v_keys_1691_ = stack[1].m_obj;
lean_object* v_vals_1692_ = stack[2].m_obj;
lean_object* v_i_1693_ = stack[3].m_obj;
lean_object* v_entries_1694_ = stack[4].m_obj;
lean_object* v_res_1713_;
v_res_1713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1690_, v_keys_1691_, v_vals_1692_, v_i_1693_, v_entries_1694_);
stack->m_obj
 = v_res_1713_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_1714_, lean_object* v_keys_1715_, lean_object* v_vals_1716_, lean_object* v_i_1717_, lean_object* v_entries_1718_){
_start:
{
size_t v_depth_boxed_1719_; lean_object* v_res_1720_; 
v_depth_boxed_1719_ = lean_unbox_usize(v_depth_1714_);
lean_dec(v_depth_1714_);
v_res_1720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_1719_, v_keys_1715_, v_vals_1716_, v_i_1717_, v_entries_1718_);
lean_dec_ref(v_vals_1716_);
lean_dec_ref(v_keys_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
size_t v_x_1141__boxed_1726_; size_t v_x_1142__boxed_1727_; lean_object* v_res_1728_; 
v_x_1141__boxed_1726_ = lean_unbox_usize(v_x_1722_);
lean_dec(v_x_1722_);
v_x_1142__boxed_1727_ = lean_unbox_usize(v_x_1723_);
lean_dec(v_x_1723_);
v_res_1728_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1721_, v_x_1141__boxed_1726_, v_x_1142__boxed_1727_, v_x_1724_, v_x_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
uint64_t v___y_1733_; 
if (lean_obj_tag(v_x_1730_) == 0)
{
uint64_t v___x_1737_; 
v___x_1737_ = 1723ULL;
v___y_1733_ = v___x_1737_;
goto v___jp_1732_;
}
else
{
uint64_t v_hash_1738_; 
v_hash_1738_ = lean_ctor_get_uint64(v_x_1730_, sizeof(void*)*2);
v___y_1733_ = v_hash_1738_;
goto v___jp_1732_;
}
v___jp_1732_:
{
size_t v___x_1734_; size_t v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_uint64_to_usize(v___y_1733_);
v___x_1735_ = ((size_t)1ULL);
v___x_1736_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1729_, v___x_1734_, v___x_1735_, v_x_1730_, v_x_1731_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
uint8_t v_stage_u2081_1742_; 
v_stage_u2081_1742_ = lean_ctor_get_uint8(v_x_1739_, sizeof(void*)*2);
if (v_stage_u2081_1742_ == 0)
{
lean_object* v_map_u2081_1743_; lean_object* v_map_u2082_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v_map_u2081_1743_ = lean_ctor_get(v_x_1739_, 0);
v_map_u2082_1744_ = lean_ctor_get(v_x_1739_, 1);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_x_1739_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1746_ = v_x_1739_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_map_u2082_1744_);
lean_inc(v_map_u2081_1743_);
lean_dec(v_x_1739_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_map_u2082_1744_, v_x_1740_, v_x_1741_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_map_u2081_1743_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v___x_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*2, v_stage_u2081_1742_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v_map_u2081_1753_; lean_object* v_map_u2082_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1762_; 
v_map_u2081_1753_ = lean_ctor_get(v_x_1739_, 0);
v_map_u2082_1754_ = lean_ctor_get(v_x_1739_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_x_1739_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1756_ = v_x_1739_;
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_map_u2082_1754_);
lean_inc(v_map_u2081_1753_);
lean_dec(v_x_1739_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1762_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_map_u2081_1753_, v_x_1740_, v_x_1741_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_map_u2082_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1761_, sizeof(void*)*2, v_stage_u2081_1742_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_addEntry(lean_object* v_s_1763_, lean_object* v_e_1764_){
_start:
{
lean_object* v_name_1765_; lean_object* v_info_1766_; lean_object* v___x_1767_; 
v_name_1765_ = lean_ctor_get(v_e_1764_, 0);
lean_inc(v_name_1765_);
v_info_1766_ = lean_ctor_get(v_e_1764_, 1);
lean_inc_ref(v_info_1766_);
lean_dec_ref(v_e_1764_);
v___x_1767_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_s_1763_, v_name_1765_, v_info_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0(lean_object* v_00_u03b2_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0___redArg(v_x_1769_, v_x_1770_, v_x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0(lean_object* v_00_u03b2_1773_, lean_object* v_x_1774_, lean_object* v_x_1775_, lean_object* v_x_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0___redArg(v_x_1774_, v_x_1775_, v_x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_1778_, lean_object* v_m_1779_, lean_object* v_a_1780_, lean_object* v_b_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1___redArg(v_m_1779_, v_a_1780_, v_b_1781_);
return v___x_1782_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1783_, lean_object* v_x_1784_, size_t v_x_1785_, size_t v_x_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___redArg(v_x_1784_, v_x_1785_, v_x_1786_, v_x_1787_, v_x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1784_ = stack[1].m_obj;
size_t v_x_1785_ = stack[2].m_num;
size_t v_x_1786_ = stack[3].m_num;
lean_object* v_x_1787_ = stack[4].m_obj;
lean_object* v_x_1788_ = stack[5].m_obj;
lean_object* v_res_1790_;
v_res_1790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(lean_box(0), v_x_1784_, v_x_1785_, v_x_1786_, v_x_1787_, v_x_1788_);
stack->m_obj
 = v_res_1790_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_){
_start:
{
size_t v_x_1510__boxed_1797_; size_t v_x_1511__boxed_1798_; lean_object* v_res_1799_; 
v_x_1510__boxed_1797_ = lean_unbox_usize(v_x_1793_);
lean_dec(v_x_1793_);
v_x_1511__boxed_1798_ = lean_unbox_usize(v_x_1794_);
lean_dec(v_x_1794_);
v_res_1799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1(v_00_u03b2_1791_, v_x_1792_, v_x_1510__boxed_1797_, v_x_1511__boxed_1798_, v_x_1795_, v_x_1796_);
return v_res_1799_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1800_, lean_object* v_a_1801_, lean_object* v_x_1802_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___redArg(v_a_1801_, v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1801_ = stack[1].m_obj;
lean_object* v_x_1802_ = stack[2].m_obj;
uint8_t v_res_1804_;
v_res_1804_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(lean_box(0), v_a_1801_, v_x_1802_);
stack->m_num = v_res_1804_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1805_, lean_object* v_a_1806_, lean_object* v_x_1807_){
_start:
{
uint8_t v_res_1808_; lean_object* v_r_1809_; 
v_res_1808_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__3(v_00_u03b2_1805_, v_a_1806_, v_x_1807_);
lean_dec(v_x_1807_);
lean_dec(v_a_1806_);
v_r_1809_ = lean_box(v_res_1808_);
return v_r_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1810_, lean_object* v_data_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4___redArg(v_data_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1813_, lean_object* v_a_1814_, lean_object* v_b_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__5___redArg(v_a_1814_, v_b_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1818_, lean_object* v_n_1819_, lean_object* v_k_1820_, lean_object* v_v_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1819_, v_k_1820_, v_v_1821_);
return v___x_1822_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1823_, size_t v_depth_1824_, lean_object* v_keys_1825_, lean_object* v_vals_1826_, lean_object* v_heq_1827_, lean_object* v_i_1828_, lean_object* v_entries_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1824_, v_keys_1825_, v_vals_1826_, v_i_1828_, v_entries_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1824_ = stack[1].m_num;
lean_object* v_keys_1825_ = stack[2].m_obj;
lean_object* v_vals_1826_ = stack[3].m_obj;
lean_object* v_i_1828_ = stack[5].m_obj;
lean_object* v_entries_1829_ = stack[6].m_obj;
lean_object* v_res_1831_;
v_res_1831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_depth_1824_, v_keys_1825_, v_vals_1826_, lean_box(0), v_i_1828_, v_entries_1829_);
stack->m_obj
 = v_res_1831_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1832_, lean_object* v_depth_1833_, lean_object* v_keys_1834_, lean_object* v_vals_1835_, lean_object* v_heq_1836_, lean_object* v_i_1837_, lean_object* v_entries_1838_){
_start:
{
size_t v_depth_boxed_1839_; lean_object* v_res_1840_; 
v_depth_boxed_1839_ = lean_unbox_usize(v_depth_1833_);
lean_dec(v_depth_1833_);
v_res_1840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1832_, v_depth_boxed_1839_, v_keys_1834_, v_vals_1835_, v_heq_1836_, v_i_1837_, v_entries_1838_);
lean_dec_ref(v_vals_1835_);
lean_dec_ref(v_keys_1834_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1841_, lean_object* v_i_1842_, lean_object* v_source_1843_, lean_object* v_target_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_1842_, v_source_1843_, v_target_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1847_, v_x_1848_, v_x_1849_, v_x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(lean_object* v_00_u03b2_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_Meta_Match_Extension_State_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_1853_, v_x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(lean_object* v_m_1856_){
_start:
{
uint8_t v_stage_u2081_1857_; 
v_stage_u2081_1857_ = lean_ctor_get_uint8(v_m_1856_, sizeof(void*)*2);
if (v_stage_u2081_1857_ == 0)
{
return v_m_1856_;
}
else
{
lean_object* v_map_u2081_1858_; lean_object* v_map_u2082_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
v_map_u2081_1858_ = lean_ctor_get(v_m_1856_, 0);
v_map_u2082_1859_ = lean_ctor_get(v_m_1856_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_m_1856_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v_m_1856_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_map_u2082_1859_);
lean_inc(v_map_u2081_1858_);
lean_dec(v_m_1856_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
uint8_t v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = 0;
if (v_isShared_1862_ == 0)
{
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_map_u2081_1858_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_map_u2082_1859_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*2, v___x_1863_);
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0(lean_object* v_00_u03b2_1868_, lean_object* v_m_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_m_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_State_switch(lean_object* v_s_1871_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v_s_1871_);
return v___x_1872_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0(lean_object* v_env_1873_, lean_object* v_as_1874_, size_t v_i_1875_, size_t v_stop_1876_, lean_object* v_b_1877_){
_start:
{
lean_object* v___y_1879_; uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_eq(v_i_1875_, v_stop_1876_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v_name_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1884_ = lean_array_uget_borrowed(v_as_1874_, v_i_1875_);
v_name_1885_ = lean_ctor_get(v___x_1884_, 0);
v___x_1886_ = 1;
lean_inc_ref(v_env_1873_);
v___x_1887_ = l_Lean_Environment_setExporting(v_env_1873_, v___x_1886_);
lean_inc(v_name_1885_);
v___x_1888_ = l_Lean_Environment_contains(v___x_1887_, v_name_1885_, v___x_1886_);
if (v___x_1888_ == 0)
{
v___y_1879_ = v_b_1877_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1889_; 
lean_inc(v___x_1884_);
v___x_1889_ = lean_array_push(v_b_1877_, v___x_1884_);
v___y_1879_ = v___x_1889_;
goto v___jp_1878_;
}
}
else
{
lean_dec_ref(v_env_1873_);
return v_b_1877_;
}
v___jp_1878_:
{
size_t v___x_1880_; size_t v___x_1881_; 
v___x_1880_ = ((size_t)1ULL);
v___x_1881_ = lean_usize_add(v_i_1875_, v___x_1880_);
v_i_1875_ = v___x_1881_;
v_b_1877_ = v___y_1879_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1873_ = stack[0].m_obj;
lean_object* v_as_1874_ = stack[1].m_obj;
size_t v_i_1875_ = stack[2].m_num;
size_t v_stop_1876_ = stack[3].m_num;
lean_object* v_b_1877_ = stack[4].m_obj;
lean_object* v_res_1890_;
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0(v_env_1873_, v_as_1874_, v_i_1875_, v_stop_1876_, v_b_1877_);
stack->m_obj
 = v_res_1890_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_1891_, lean_object* v_as_1892_, lean_object* v_i_1893_, lean_object* v_stop_1894_, lean_object* v_b_1895_){
_start:
{
size_t v_i_boxed_1896_; size_t v_stop_boxed_1897_; lean_object* v_res_1898_; 
v_i_boxed_1896_ = lean_unbox_usize(v_i_1893_);
lean_dec(v_i_1893_);
v_stop_boxed_1897_ = lean_unbox_usize(v_stop_1894_);
lean_dec(v_stop_1894_);
v_res_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0(v_env_1891_, v_as_1892_, v_i_boxed_1896_, v_stop_boxed_1897_, v_b_1895_);
lean_dec_ref(v_as_1892_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(lean_object* v_env_1901_, lean_object* v_x_1902_, lean_object* v_entries_1903_){
_start:
{
lean_object* v_all_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_all_1904_ = lean_array_mk(v_entries_1903_);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = lean_array_get_size(v_all_1904_);
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_));
v___x_1908_ = lean_nat_dec_lt(v___x_1905_, v___x_1906_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
lean_dec_ref(v_env_1901_);
v___x_1909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1907_);
lean_ctor_set(v___x_1909_, 2, v_all_1904_);
return v___x_1909_;
}
else
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_nat_dec_le(v___x_1906_, v___x_1906_);
if (v___x_1910_ == 0)
{
if (v___x_1908_ == 0)
{
lean_object* v___x_1911_; 
lean_dec_ref(v_env_1901_);
v___x_1911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1907_);
lean_ctor_set(v___x_1911_, 1, v___x_1907_);
lean_ctor_set(v___x_1911_, 2, v_all_1904_);
return v___x_1911_;
}
else
{
size_t v___x_1912_; size_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1912_ = ((size_t)0ULL);
v___x_1913_ = lean_usize_of_nat(v___x_1906_);
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0(v_env_1901_, v_all_1904_, v___x_1912_, v___x_1913_, v___x_1907_);
lean_inc_ref(v___x_1914_);
v___x_1915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
lean_ctor_set(v___x_1915_, 2, v_all_1904_);
return v___x_1915_;
}
}
else
{
size_t v___x_1916_; size_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = ((size_t)0ULL);
v___x_1917_ = lean_usize_of_nat(v___x_1906_);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__0(v_env_1901_, v_all_1904_, v___x_1916_, v___x_1917_, v___x_1907_);
lean_inc_ref(v___x_1918_);
v___x_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
lean_ctor_set(v___x_1919_, 2, v_all_1904_);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed(lean_object* v_env_1920_, lean_object* v_x_1921_, lean_object* v_entries_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__0_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(v_env_1920_, v_x_1921_, v_entries_1922_);
lean_dec_ref(v_x_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__1_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(lean_object* v_es_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_array_mk(v_es_1924_);
return v___x_1925_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_1926_, size_t v_i_1927_, size_t v_stop_1928_, lean_object* v_b_1929_){
_start:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_eq(v_i_1927_, v_stop_1928_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; 
v___x_1931_ = lean_array_uget_borrowed(v_as_1926_, v_i_1927_);
lean_inc(v___x_1931_);
v___x_1932_ = l_Lean_Meta_Match_Extension_State_addEntry(v_b_1929_, v___x_1931_);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1927_, v___x_1933_);
v_i_1927_ = v___x_1934_;
v_b_1929_ = v___x_1932_;
goto _start;
}
else
{
return v_b_1929_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1926_ = stack[0].m_obj;
size_t v_i_1927_ = stack[1].m_num;
size_t v_stop_1928_ = stack[2].m_num;
lean_object* v_b_1929_ = stack[3].m_obj;
lean_object* v_res_1936_;
v_res_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1(v_as_1926_, v_i_1927_, v_stop_1928_, v_b_1929_);
stack->m_obj
 = v_res_1936_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_1937_, lean_object* v_i_1938_, lean_object* v_stop_1939_, lean_object* v_b_1940_){
_start:
{
size_t v_i_boxed_1941_; size_t v_stop_boxed_1942_; lean_object* v_res_1943_; 
v_i_boxed_1941_ = lean_unbox_usize(v_i_1938_);
lean_dec(v_i_1938_);
v_stop_boxed_1942_ = lean_unbox_usize(v_stop_1939_);
lean_dec(v_stop_1939_);
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1(v_as_1937_, v_i_boxed_1941_, v_stop_boxed_1942_, v_b_1940_);
lean_dec_ref(v_as_1937_);
return v_res_1943_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_1944_, size_t v_i_1945_, size_t v_stop_1946_, lean_object* v_b_1947_){
_start:
{
lean_object* v___y_1949_; uint8_t v___x_1953_; 
v___x_1953_ = lean_usize_dec_eq(v_i_1945_, v_stop_1946_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1954_ = lean_array_uget_borrowed(v_as_1944_, v_i_1945_);
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_array_get_size(v___x_1954_);
v___x_1957_ = lean_nat_dec_lt(v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
v___y_1949_ = v_b_1947_;
goto v___jp_1948_;
}
else
{
size_t v___x_1958_; size_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = lean_usize_of_nat(v___x_1956_);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__1(v___x_1954_, v___x_1958_, v___x_1959_, v_b_1947_);
v___y_1949_ = v___x_1960_;
goto v___jp_1948_;
}
}
else
{
return v_b_1947_;
}
v___jp_1948_:
{
size_t v___x_1950_; size_t v___x_1951_; 
v___x_1950_ = ((size_t)1ULL);
v___x_1951_ = lean_usize_add(v_i_1945_, v___x_1950_);
v_i_1945_ = v___x_1951_;
v_b_1947_ = v___y_1949_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1944_ = stack[0].m_obj;
size_t v_i_1945_ = stack[1].m_num;
size_t v_stop_1946_ = stack[2].m_num;
lean_object* v_b_1947_ = stack[3].m_obj;
lean_object* v_res_1961_;
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2(v_as_1944_, v_i_1945_, v_stop_1946_, v_b_1947_);
stack->m_obj
 = v_res_1961_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_1962_, lean_object* v_i_1963_, lean_object* v_stop_1964_, lean_object* v_b_1965_){
_start:
{
size_t v_i_boxed_1966_; size_t v_stop_boxed_1967_; lean_object* v_res_1968_; 
v_i_boxed_1966_ = lean_unbox_usize(v_i_1963_);
lean_dec(v_i_1963_);
v_stop_boxed_1967_ = lean_unbox_usize(v_stop_1964_);
lean_dec(v_stop_1964_);
v_res_1968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2(v_as_1962_, v_i_boxed_1966_, v_stop_boxed_1967_, v_b_1965_);
lean_dec_ref(v_as_1962_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1(lean_object* v_initState_1969_, lean_object* v_as_1970_){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1972_ = lean_array_get_size(v_as_1970_);
v___x_1973_ = lean_nat_dec_lt(v___x_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
return v_initState_1969_;
}
else
{
size_t v___x_1974_; size_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = ((size_t)0ULL);
v___x_1975_ = lean_usize_of_nat(v___x_1972_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1_spec__2(v_as_1970_, v___x_1974_, v___x_1975_, v_initState_1969_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_1977_, lean_object* v_as_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1(v_initState_1977_, v_as_1978_);
lean_dec_ref(v_as_1978_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(lean_object* v_es_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_obj_once(&l_Lean_Meta_Match_Extension_instInhabitedState___closed__4, &l_Lean_Meta_Match_Extension_instInhabitedState___closed__4_once, _init_l_Lean_Meta_Match_Extension_instInhabitedState___closed__4);
v___x_1982_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__spec__1(v___x_1981_, v_es_1980_);
v___x_1983_ = l_Lean_SMap_switch___at___00Lean_Meta_Match_Extension_State_switch_spec__0___redArg(v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed(lean_object* v_es_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___lam__2_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(v_es_1984_);
lean_dec_ref(v_es_1984_);
return v_res_1985_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn___closed__12_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_));
v___x_2016_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2015_);
return v___x_2016_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2017_;
v_res_2017_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2____boxed(lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_();
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo___lam__0(lean_object* v___x_2020_, lean_object* v___x_2021_, lean_object* v_s_2022_){
_start:
{
lean_object* v_addEntryFn_2023_; lean_object* v_importedEntries_2024_; lean_object* v_state_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2033_; 
v_addEntryFn_2023_ = lean_ctor_get(v___x_2020_, 3);
lean_inc(v_addEntryFn_2023_);
lean_dec_ref(v___x_2020_);
v_importedEntries_2024_ = lean_ctor_get(v_s_2022_, 0);
v_state_2025_ = lean_ctor_get(v_s_2022_, 1);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_s_2022_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2027_ = v_s_2022_;
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_state_2025_);
lean_inc(v_importedEntries_2024_);
lean_dec(v_s_2022_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2033_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_state_2029_; lean_object* v___x_2031_; 
v_state_2029_ = lean_apply_2(v_addEntryFn_2023_, v_state_2025_, v___x_2021_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v_state_2029_);
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_importedEntries_2024_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_state_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object* v_env_2034_, lean_object* v_matcherName_2035_, lean_object* v_info_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v_toEnvExtension_2038_; lean_object* v_asyncMode_2039_; uint8_t v_logWrites_2040_; lean_object* v___x_2041_; lean_object* v___f_2042_; uint8_t v___x_2043_; 
v___x_2037_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2038_ = lean_ctor_get(v___x_2037_, 0);
v_asyncMode_2039_ = lean_ctor_get(v_toEnvExtension_2038_, 2);
v_logWrites_2040_ = lean_ctor_get_uint8(v_toEnvExtension_2038_, sizeof(void*)*6);
lean_inc(v_matcherName_2035_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v_matcherName_2035_);
lean_ctor_set(v___x_2041_, 1, v_info_2036_);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_Extension_addMatcherInfo___lam__0), 3, 2);
lean_closure_set(v___f_2042_, 0, v___x_2037_);
lean_closure_set(v___f_2042_, 1, v___x_2041_);
v___x_2043_ = 1;
if (v_logWrites_2040_ == 0)
{
lean_object* v___x_2044_; 
lean_inc_ref(v_toEnvExtension_2038_);
v___x_2044_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2038_, v_env_2034_, v___f_2042_, v_asyncMode_2039_, v_matcherName_2035_, v___x_2043_);
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_inc(v_matcherName_2035_);
v___x_2045_ = l_Lean_Environment_logDeclChange(v_env_2034_, v_matcherName_2035_);
lean_inc_ref(v_toEnvExtension_2038_);
v___x_2046_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2038_, v___x_2045_, v___f_2042_, v_asyncMode_2039_, v_matcherName_2035_, v___x_2043_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_2047_, lean_object* v_vals_2048_, lean_object* v_i_2049_, lean_object* v_k_2050_){
_start:
{
lean_object* v___x_2051_; uint8_t v___x_2052_; 
v___x_2051_ = lean_array_get_size(v_keys_2047_);
v___x_2052_ = lean_nat_dec_lt(v_i_2049_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
lean_dec(v_i_2049_);
v___x_2053_ = lean_box(0);
return v___x_2053_;
}
else
{
lean_object* v_k_x27_2054_; uint8_t v___x_2055_; 
v_k_x27_2054_ = lean_array_fget_borrowed(v_keys_2047_, v_i_2049_);
v___x_2055_ = lean_name_eq(v_k_2050_, v_k_x27_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_add(v_i_2049_, v___x_2056_);
lean_dec(v_i_2049_);
v_i_2049_ = v___x_2057_;
goto _start;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_array_fget_borrowed(v_vals_2048_, v_i_2049_);
lean_dec(v_i_2049_);
lean_inc(v___x_2059_);
v___x_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
return v___x_2060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2061_, lean_object* v_vals_2062_, lean_object* v_i_2063_, lean_object* v_k_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2061_, v_vals_2062_, v_i_2063_, v_k_2064_);
lean_dec(v_k_2064_);
lean_dec_ref(v_vals_2062_);
lean_dec_ref(v_keys_2061_);
return v_res_2065_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2066_, size_t v_x_2067_, lean_object* v_x_2068_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
lean_object* v_es_2069_; lean_object* v___x_2070_; size_t v___x_2071_; size_t v___x_2072_; lean_object* v_j_2073_; lean_object* v___x_2074_; 
v_es_2069_ = lean_ctor_get(v_x_2066_, 0);
v___x_2070_ = lean_box(2);
v___x_2071_ = ((size_t)31ULL);
v___x_2072_ = lean_usize_land(v_x_2067_, v___x_2071_);
v_j_2073_ = lean_usize_to_nat(v___x_2072_);
v___x_2074_ = lean_array_get_borrowed(v___x_2070_, v_es_2069_, v_j_2073_);
lean_dec(v_j_2073_);
switch(lean_obj_tag(v___x_2074_))
{
case 0:
{
lean_object* v_key_2075_; lean_object* v_val_2076_; uint8_t v___x_2077_; 
v_key_2075_ = lean_ctor_get(v___x_2074_, 0);
v_val_2076_ = lean_ctor_get(v___x_2074_, 1);
v___x_2077_ = lean_name_eq(v_x_2068_, v_key_2075_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_box(0);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; 
lean_inc(v_val_2076_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_val_2076_);
return v___x_2079_;
}
}
case 1:
{
lean_object* v_node_2080_; size_t v___x_2081_; size_t v___x_2082_; 
v_node_2080_ = lean_ctor_get(v___x_2074_, 0);
v___x_2081_ = ((size_t)5ULL);
v___x_2082_ = lean_usize_shift_right(v_x_2067_, v___x_2081_);
v_x_2066_ = v_node_2080_;
v_x_2067_ = v___x_2082_;
goto _start;
}
default: 
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_box(0);
return v___x_2084_;
}
}
}
else
{
lean_object* v_ks_2085_; lean_object* v_vs_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_ks_2085_ = lean_ctor_get(v_x_2066_, 0);
v_vs_2086_ = lean_ctor_get(v_x_2066_, 1);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_2085_, v_vs_2086_, v___x_2087_, v_x_2068_);
return v___x_2088_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2066_ = stack[0].m_obj;
size_t v_x_2067_ = stack[1].m_num;
lean_object* v_x_2068_ = stack[2].m_obj;
lean_object* v_res_2089_;
v_res_2089_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2066_, v_x_2067_, v_x_2068_);
stack->m_obj
 = v_res_2089_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_){
_start:
{
size_t v_x_541__boxed_2093_; lean_object* v_res_2094_; 
v_x_541__boxed_2093_ = lean_unbox_usize(v_x_2091_);
lean_dec(v_x_2091_);
v_res_2094_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2090_, v_x_541__boxed_2093_, v_x_2092_);
lean_dec(v_x_2092_);
lean_dec_ref(v_x_2090_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_2095_, lean_object* v_x_2096_){
_start:
{
uint64_t v___y_2098_; 
if (lean_obj_tag(v_x_2096_) == 0)
{
uint64_t v___x_2101_; 
v___x_2101_ = 1723ULL;
v___y_2098_ = v___x_2101_;
goto v___jp_2097_;
}
else
{
uint64_t v_hash_2102_; 
v_hash_2102_ = lean_ctor_get_uint64(v_x_2096_, sizeof(void*)*2);
v___y_2098_ = v_hash_2102_;
goto v___jp_2097_;
}
v___jp_2097_:
{
size_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_uint64_to_usize(v___y_2098_);
v___x_2100_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2095_, v___x_2099_, v_x_2096_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2103_, v_x_2104_);
lean_dec(v_x_2104_);
lean_dec_ref(v_x_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(lean_object* v_a_2106_, lean_object* v_x_2107_){
_start:
{
if (lean_obj_tag(v_x_2107_) == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_box(0);
return v___x_2108_;
}
else
{
lean_object* v_key_2109_; lean_object* v_value_2110_; lean_object* v_tail_2111_; uint8_t v___x_2112_; 
v_key_2109_ = lean_ctor_get(v_x_2107_, 0);
v_value_2110_ = lean_ctor_get(v_x_2107_, 1);
v_tail_2111_ = lean_ctor_get(v_x_2107_, 2);
v___x_2112_ = lean_name_eq(v_key_2109_, v_a_2106_);
if (v___x_2112_ == 0)
{
v_x_2107_ = v_tail_2111_;
goto _start;
}
else
{
lean_object* v___x_2114_; 
lean_inc(v_value_2110_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_value_2110_);
return v___x_2114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2115_, v_x_2116_);
lean_dec(v_x_2116_);
lean_dec(v_a_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(lean_object* v_m_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_buckets_2120_; lean_object* v___x_2121_; uint64_t v___y_2123_; 
v_buckets_2120_ = lean_ctor_get(v_m_2118_, 1);
v___x_2121_ = lean_array_get_size(v_buckets_2120_);
if (lean_obj_tag(v_a_2119_) == 0)
{
uint64_t v___x_2137_; 
v___x_2137_ = 1723ULL;
v___y_2123_ = v___x_2137_;
goto v___jp_2122_;
}
else
{
uint64_t v_hash_2138_; 
v_hash_2138_ = lean_ctor_get_uint64(v_a_2119_, sizeof(void*)*2);
v___y_2123_ = v_hash_2138_;
goto v___jp_2122_;
}
v___jp_2122_:
{
uint64_t v___x_2124_; uint64_t v___x_2125_; uint64_t v_fold_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; uint64_t v___x_2129_; size_t v___x_2130_; size_t v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2124_ = 32ULL;
v___x_2125_ = lean_uint64_shift_right(v___y_2123_, v___x_2124_);
v_fold_2126_ = lean_uint64_xor(v___y_2123_, v___x_2125_);
v___x_2127_ = 16ULL;
v___x_2128_ = lean_uint64_shift_right(v_fold_2126_, v___x_2127_);
v___x_2129_ = lean_uint64_xor(v_fold_2126_, v___x_2128_);
v___x_2130_ = lean_uint64_to_usize(v___x_2129_);
v___x_2131_ = lean_usize_of_nat(v___x_2121_);
v___x_2132_ = ((size_t)1ULL);
v___x_2133_ = lean_usize_sub(v___x_2131_, v___x_2132_);
v___x_2134_ = lean_usize_land(v___x_2130_, v___x_2133_);
v___x_2135_ = lean_array_uget_borrowed(v_buckets_2120_, v___x_2134_);
v___x_2136_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2119_, v___x_2135_);
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_m_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_m_2139_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
uint8_t v_stage_u2081_2144_; 
v_stage_u2081_2144_ = lean_ctor_get_uint8(v_x_2142_, sizeof(void*)*2);
if (v_stage_u2081_2144_ == 0)
{
lean_object* v_map_u2081_2145_; lean_object* v_map_u2082_2146_; lean_object* v___x_2147_; 
v_map_u2081_2145_ = lean_ctor_get(v_x_2142_, 0);
v_map_u2082_2146_ = lean_ctor_get(v_x_2142_, 1);
v___x_2147_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_map_u2082_2146_, v_x_2143_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2145_, v_x_2143_);
return v___x_2148_;
}
else
{
return v___x_2147_;
}
}
else
{
lean_object* v_map_u2081_2149_; lean_object* v___x_2150_; 
v_map_u2081_2149_ = lean_ctor_get(v_x_2142_, 0);
v___x_2150_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_map_u2081_2149_, v_x_2143_);
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2151_, v_x_2152_);
lean_dec(v_x_2152_);
lean_dec_ref(v_x_2151_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object* v_env_2155_, lean_object* v_declName_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Name_eraseMacroScopes(v_declName_2156_);
if (lean_obj_tag(v___x_2157_) == 1)
{
lean_object* v_str_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v_str_2158_ = lean_ctor_get(v___x_2157_, 1);
lean_inc_ref(v_str_2158_);
lean_dec_ref_known(v___x_2157_, 2);
v___x_2159_ = lean_string_utf8_byte_size(v_str_2158_);
v___x_2160_ = lean_unsigned_to_nat(6u);
v___x_2161_ = lean_nat_dec_le(v___x_2160_, v___x_2159_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_dec_ref(v_str_2158_);
lean_dec(v_declName_2156_);
lean_dec_ref(v_env_2155_);
v___x_2162_ = lean_box(0);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = ((lean_object*)(l_Lean_Meta_Match_Extension_getMatcherInfo_x3f___closed__0));
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_string_memcmp(v_str_2158_, v___x_2163_, v___x_2164_, v___x_2164_, v___x_2160_);
lean_dec_ref(v_str_2158_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_dec(v_declName_2156_);
lean_dec_ref(v_env_2155_);
v___x_2166_ = lean_box(0);
return v___x_2166_;
}
else
{
lean_object* v___x_2167_; lean_object* v_toEnvExtension_2168_; lean_object* v_asyncMode_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2167_ = l_Lean_Meta_Match_Extension_extension;
v_toEnvExtension_2168_ = lean_ctor_get(v___x_2167_, 0);
v_asyncMode_2169_ = lean_ctor_get(v_toEnvExtension_2168_, 2);
v___x_2170_ = l_Lean_Meta_Match_Extension_instInhabitedState;
lean_inc(v_declName_2156_);
v___x_2171_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2170_, v___x_2167_, v_env_2155_, v_asyncMode_2169_, v_declName_2156_);
v___x_2172_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v___x_2171_, v_declName_2156_);
lean_dec(v_declName_2156_);
lean_dec(v___x_2171_);
return v___x_2172_;
}
}
}
else
{
lean_object* v___x_2173_; 
lean_dec(v___x_2157_);
lean_dec(v_declName_2156_);
lean_dec_ref(v_env_2155_);
v___x_2173_ = lean_box(0);
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(lean_object* v_00_u03b2_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___redArg(v_x_2175_, v_x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0(v_00_u03b2_2178_, v_x_2179_, v_x_2180_);
lean_dec(v_x_2180_);
lean_dec_ref(v_x_2179_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___redArg(v_x_2183_, v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0(v_00_u03b2_2186_, v_x_2187_, v_x_2188_);
lean_dec(v_x_2188_);
lean_dec_ref(v_x_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(lean_object* v_00_u03b2_2190_, lean_object* v_m_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___redArg(v_m_2191_, v_a_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2194_, lean_object* v_m_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1(v_00_u03b2_2194_, v_m_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_m_2195_);
return v_res_2197_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2198_, lean_object* v_x_2199_, size_t v_x_2200_, lean_object* v_x_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___redArg(v_x_2199_, v_x_2200_, v_x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2199_ = stack[1].m_obj;
size_t v_x_2200_ = stack[2].m_num;
lean_object* v_x_2201_ = stack[3].m_obj;
lean_object* v_res_2203_;
v_res_2203_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(lean_box(0), v_x_2199_, v_x_2200_, v_x_2201_);
stack->m_obj
 = v_res_2203_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2204_, lean_object* v_x_2205_, lean_object* v_x_2206_, lean_object* v_x_2207_){
_start:
{
size_t v_x_827__boxed_2208_; lean_object* v_res_2209_; 
v_x_827__boxed_2208_ = lean_unbox_usize(v_x_2206_);
lean_dec(v_x_2206_);
v_res_2209_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2204_, v_x_2205_, v_x_827__boxed_2208_, v_x_2207_);
lean_dec(v_x_2207_);
lean_dec_ref(v_x_2205_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2210_, lean_object* v_a_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___redArg(v_a_2211_, v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2214_, lean_object* v_a_2215_, lean_object* v_x_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__1_spec__3(v_00_u03b2_2214_, v_a_2215_, v_x_2216_);
lean_dec(v_x_2216_);
lean_dec(v_a_2215_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2218_, lean_object* v_keys_2219_, lean_object* v_vals_2220_, lean_object* v_heq_2221_, lean_object* v_i_2222_, lean_object* v_k_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2219_, v_vals_2220_, v_i_2222_, v_k_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2225_, lean_object* v_keys_2226_, lean_object* v_vals_2227_, lean_object* v_heq_2228_, lean_object* v_i_2229_, lean_object* v_k_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Meta_Match_Extension_getMatcherInfo_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2225_, v_keys_2226_, v_vals_2227_, v_heq_2228_, v_i_2229_, v_k_2230_);
lean_dec(v_k_2230_);
lean_dec_ref(v_vals_2227_);
lean_dec_ref(v_keys_2226_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0(lean_object* v_matcherName_2232_, lean_object* v_info_2233_, lean_object* v_env_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2234_, v_matcherName_2232_, v_info_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___redArg(lean_object* v_inst_2236_, lean_object* v_matcherName_2237_, lean_object* v_info_2238_){
_start:
{
lean_object* v_modifyEnv_2239_; lean_object* v___f_2240_; lean_object* v___x_2241_; 
v_modifyEnv_2239_ = lean_ctor_get(v_inst_2236_, 1);
lean_inc(v_modifyEnv_2239_);
lean_dec_ref(v_inst_2236_);
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_addMatcherInfo___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2240_, 0, v_matcherName_2237_);
lean_closure_set(v___f_2240_, 1, v_info_2238_);
v___x_2241_ = lean_apply_1(v_modifyEnv_2239_, v___f_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo(lean_object* v_m_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_matcherName_2245_, lean_object* v_info_2246_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Meta_Match_addMatcherInfo___redArg(v_inst_2244_, v_matcherName_2245_, v_info_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___boxed(lean_object* v_m_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_matcherName_2251_, lean_object* v_info_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Meta_Match_addMatcherInfo(v_m_2248_, v_inst_2249_, v_inst_2250_, v_matcherName_2251_, v_info_2252_);
lean_dec_ref(v_inst_2249_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfoCore_x3f(lean_object* v_env_2254_, lean_object* v_declName_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2254_, v_declName_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0(lean_object* v_declName_2257_, lean_object* v_toPure_2258_, lean_object* v_____do__lift_2259_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_____do__lift_2259_, v_declName_2257_);
v___x_2261_ = lean_apply_2(v_toPure_2258_, lean_box(0), v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_declName_2264_){
_start:
{
lean_object* v_toApplicative_2265_; lean_object* v_toBind_2266_; lean_object* v_getEnv_2267_; lean_object* v_toPure_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; 
v_toApplicative_2265_ = lean_ctor_get(v_inst_2262_, 0);
lean_inc_ref(v_toApplicative_2265_);
v_toBind_2266_ = lean_ctor_get(v_inst_2262_, 1);
lean_inc(v_toBind_2266_);
lean_dec_ref(v_inst_2262_);
v_getEnv_2267_ = lean_ctor_get(v_inst_2263_, 0);
lean_inc(v_getEnv_2267_);
lean_dec_ref(v_inst_2263_);
v_toPure_2268_ = lean_ctor_get(v_toApplicative_2265_, 1);
lean_inc(v_toPure_2268_);
lean_dec_ref(v_toApplicative_2265_);
v___f_2269_ = lean_alloc_closure((void*)(l_Lean_Meta_getMatcherInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2269_, 0, v_declName_2264_);
lean_closure_set(v___f_2269_, 1, v_toPure_2268_);
v___x_2270_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v_getEnv_2267_, v___f_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object* v_m_2271_, lean_object* v_inst_2272_, lean_object* v_inst_2273_, lean_object* v_declName_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_2272_, v_inst_2273_, v_declName_2274_);
return v___x_2275_;
}
}
uint8_t l_Lean_Meta_isMatcherCore(lean_object* v_env_2276_, lean_object* v_declName_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2276_, v_declName_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
uint8_t v___x_2279_; 
v___x_2279_ = 0;
return v___x_2279_;
}
else
{
uint8_t v___x_2280_; 
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = 1;
return v___x_2280_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2276_ = stack[0].m_obj;
lean_object* v_declName_2277_ = stack[1].m_obj;
uint8_t v_res_2281_;
v_res_2281_ = l_Lean_Meta_isMatcherCore(v_env_2276_, v_declName_2277_);
stack->m_num = v_res_2281_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherCore___boxed(lean_object* v_env_2282_, lean_object* v_declName_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Lean_Meta_isMatcherCore(v_env_2282_, v_declName_2283_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg___lam__0(lean_object* v_declName_2286_, lean_object* v_toPure_2287_, lean_object* v_____do__lift_2288_){
_start:
{
uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = l_Lean_Meta_isMatcherCore(v_____do__lift_2288_, v_declName_2286_);
v___x_2290_ = lean_box(v___x_2289_);
v___x_2291_ = lean_apply_2(v_toPure_2287_, lean_box(0), v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___redArg(lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_declName_2294_){
_start:
{
lean_object* v_toApplicative_2295_; lean_object* v_toBind_2296_; lean_object* v_getEnv_2297_; lean_object* v_toPure_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; 
v_toApplicative_2295_ = lean_ctor_get(v_inst_2292_, 0);
lean_inc_ref(v_toApplicative_2295_);
v_toBind_2296_ = lean_ctor_get(v_inst_2292_, 1);
lean_inc(v_toBind_2296_);
lean_dec_ref(v_inst_2292_);
v_getEnv_2297_ = lean_ctor_get(v_inst_2293_, 0);
lean_inc(v_getEnv_2297_);
lean_dec_ref(v_inst_2293_);
v_toPure_2298_ = lean_ctor_get(v_toApplicative_2295_, 1);
lean_inc(v_toPure_2298_);
lean_dec_ref(v_toApplicative_2295_);
v___f_2299_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcher___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2299_, 0, v_declName_2294_);
lean_closure_set(v___f_2299_, 1, v_toPure_2298_);
v___x_2300_ = lean_apply_4(v_toBind_2296_, lean_box(0), lean_box(0), v_getEnv_2297_, v___f_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher(lean_object* v_m_2301_, lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_declName_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Meta_isMatcher___redArg(v_inst_2302_, v_inst_2303_, v_declName_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object* v_env_2306_, lean_object* v_e_2307_){
_start:
{
lean_object* v_fn_2308_; uint8_t v___x_2309_; 
v_fn_2308_ = l_Lean_Expr_getAppFn(v_e_2307_);
v___x_2309_ = l_Lean_Expr_isConst(v_fn_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; 
lean_dec_ref(v_fn_2308_);
lean_dec_ref(v_env_2306_);
v___x_2310_ = lean_box(0);
return v___x_2310_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = l_Lean_Expr_constName_x21(v_fn_2308_);
lean_dec_ref(v_fn_2308_);
v___x_2312_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2306_, v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 1)
{
lean_object* v_val_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v_val_2313_ = lean_ctor_get(v___x_2312_, 0);
v___x_2314_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2313_);
v___x_2315_ = l_Lean_Expr_getAppNumArgs(v_e_2307_);
v___x_2316_ = lean_nat_dec_le(v___x_2314_, v___x_2315_);
lean_dec(v___x_2315_);
lean_dec(v___x_2314_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; 
lean_dec_ref_known(v___x_2312_, 1);
v___x_2317_ = lean_box(0);
return v___x_2317_;
}
else
{
return v___x_2312_;
}
}
else
{
lean_object* v___x_2318_; 
lean_dec(v___x_2312_);
v___x_2318_ = lean_box(0);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore_x3f___boxed(lean_object* v_env_2319_, lean_object* v_e_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2319_, v_e_2320_);
lean_dec_ref(v_e_2320_);
return v_res_2321_;
}
}
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object* v_env_2322_, lean_object* v_e_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_2322_, v_e_2323_);
if (lean_obj_tag(v___x_2324_) == 0)
{
uint8_t v___x_2325_; 
v___x_2325_ = 0;
return v___x_2325_;
}
else
{
uint8_t v___x_2326_; 
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = 1;
return v___x_2326_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherAppCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2322_ = stack[0].m_obj;
lean_object* v_e_2323_ = stack[1].m_obj;
uint8_t v_res_2327_;
v_res_2327_ = l_Lean_Meta_isMatcherAppCore(v_env_2322_, v_e_2323_);
stack->m_num = v_res_2327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherAppCore___boxed(lean_object* v_env_2328_, lean_object* v_e_2329_){
_start:
{
uint8_t v_res_2330_; lean_object* v_r_2331_; 
v_res_2330_ = l_Lean_Meta_isMatcherAppCore(v_env_2328_, v_e_2329_);
lean_dec_ref(v_e_2329_);
v_r_2331_ = lean_box(v_res_2330_);
return v_r_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0(lean_object* v_e_2332_, lean_object* v_toPure_2333_, lean_object* v_____do__lift_2334_){
_start:
{
uint8_t v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = l_Lean_Meta_isMatcherAppCore(v_____do__lift_2334_, v_e_2332_);
v___x_2336_ = lean_box(v___x_2335_);
v___x_2337_ = lean_apply_2(v_toPure_2333_, lean_box(0), v___x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed(lean_object* v_e_2338_, lean_object* v_toPure_2339_, lean_object* v_____do__lift_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Meta_isMatcherApp___redArg___lam__0(v_e_2338_, v_toPure_2339_, v_____do__lift_2340_);
lean_dec_ref(v_e_2338_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___redArg(lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_e_2344_){
_start:
{
lean_object* v_toApplicative_2345_; lean_object* v_toBind_2346_; lean_object* v_getEnv_2347_; lean_object* v_toPure_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; 
v_toApplicative_2345_ = lean_ctor_get(v_inst_2342_, 0);
lean_inc_ref(v_toApplicative_2345_);
v_toBind_2346_ = lean_ctor_get(v_inst_2342_, 1);
lean_inc(v_toBind_2346_);
lean_dec_ref(v_inst_2342_);
v_getEnv_2347_ = lean_ctor_get(v_inst_2343_, 0);
lean_inc(v_getEnv_2347_);
lean_dec_ref(v_inst_2343_);
v_toPure_2348_ = lean_ctor_get(v_toApplicative_2345_, 1);
lean_inc(v_toPure_2348_);
lean_dec_ref(v_toApplicative_2345_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherApp___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2349_, 0, v_e_2344_);
lean_closure_set(v___f_2349_, 1, v_toPure_2348_);
v___x_2350_ = lean_apply_4(v_toBind_2346_, lean_box(0), lean_box(0), v_getEnv_2347_, v___f_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp(lean_object* v_m_2351_, lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_e_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_Meta_isMatcherApp___redArg(v_inst_2352_, v_inst_2353_, v_e_2354_);
return v___x_2355_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_));
v___x_2363_ = lean_box(0);
v___x_2364_ = 0;
v___x_2365_ = l_Lean_mkTagDeclarationExtension(v___x_2362_, v___x_2363_, v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2366_;
v_res_2366_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2366_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2____boxed(lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Match_MatcherInfo_3189009982____hygCtx___hyg_2_();
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markMatcherLike(lean_object* v_env_2369_, lean_object* v_declName_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = l_Lean_Meta_matcherLikeExt;
v___x_2372_ = l_Lean_TagDeclarationExtension_tag(v___x_2371_, v_env_2369_, v_declName_2370_);
return v___x_2372_;
}
}
uint8_t l_Lean_Meta_isMatcherLikeCore(lean_object* v_env_2373_, lean_object* v_declName_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v_toEnvExtension_2376_; lean_object* v_asyncMode_2377_; uint8_t v___x_2378_; 
v___x_2375_ = l_Lean_Meta_matcherLikeExt;
v_toEnvExtension_2376_ = lean_ctor_get(v___x_2375_, 0);
v_asyncMode_2377_ = lean_ctor_get(v_toEnvExtension_2376_, 2);
v___x_2378_ = l_Lean_TagDeclarationExtension_isTagged(v___x_2375_, v_env_2373_, v_declName_2374_, v_asyncMode_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherLikeCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2373_ = stack[0].m_obj;
lean_object* v_declName_2374_ = stack[1].m_obj;
uint8_t v_res_2379_;
v_res_2379_ = l_Lean_Meta_isMatcherLikeCore(v_env_2373_, v_declName_2374_);
stack->m_num = v_res_2379_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLikeCore___boxed(lean_object* v_env_2380_, lean_object* v_declName_2381_){
_start:
{
uint8_t v_res_2382_; lean_object* v_r_2383_; 
v_res_2382_ = l_Lean_Meta_isMatcherLikeCore(v_env_2380_, v_declName_2381_);
v_r_2383_ = lean_box(v_res_2382_);
return v_r_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg___lam__0(lean_object* v_declName_2384_, lean_object* v_toPure_2385_, lean_object* v_____do__lift_2386_){
_start:
{
uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = l_Lean_Meta_isMatcherLikeCore(v_____do__lift_2386_, v_declName_2384_);
v___x_2388_ = lean_box(v___x_2387_);
v___x_2389_ = lean_apply_2(v_toPure_2385_, lean_box(0), v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike___redArg(lean_object* v_inst_2390_, lean_object* v_inst_2391_, lean_object* v_declName_2392_){
_start:
{
lean_object* v_toApplicative_2393_; lean_object* v_toBind_2394_; lean_object* v_getEnv_2395_; lean_object* v_toPure_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; 
v_toApplicative_2393_ = lean_ctor_get(v_inst_2390_, 0);
lean_inc_ref(v_toApplicative_2393_);
v_toBind_2394_ = lean_ctor_get(v_inst_2390_, 1);
lean_inc(v_toBind_2394_);
lean_dec_ref(v_inst_2390_);
v_getEnv_2395_ = lean_ctor_get(v_inst_2391_, 0);
lean_inc(v_getEnv_2395_);
lean_dec_ref(v_inst_2391_);
v_toPure_2396_ = lean_ctor_get(v_toApplicative_2393_, 1);
lean_inc(v_toPure_2396_);
lean_dec_ref(v_toApplicative_2393_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_Meta_isMatcherLike___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2397_, 0, v_declName_2392_);
lean_closure_set(v___f_2397_, 1, v_toPure_2396_);
v___x_2398_ = lean_apply_4(v_toBind_2394_, lean_box(0), lean_box(0), v_getEnv_2395_, v___f_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherLike(lean_object* v_m_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_declName_2402_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Meta_isMatcherLike___redArg(v_inst_2400_, v_inst_2401_, v_declName_2402_);
return v___x_2403_;
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
res = l___private_Lean_Meta_Match_MatcherInfo_0__Lean_Meta_Match_Extension_initFn_00___x40_Lean_Meta_Match_MatcherInfo_2587217507____hygCtx___hyg_2_();
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
