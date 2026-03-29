// Lean compiler output
// Module: Std.Internal.Http.Data.Headers
// Imports: public import Std.Internal.Http.Data.Headers.Basic public import Std.Internal.Http.Data.Headers.Name public import Std.Internal.Http.Data.Headers.Value
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_Header_instReprName_repr___redArg(lean_object*);
lean_object* l_Std_Http_Header_instReprValue_repr___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
static const lean_array_object l_Std_Http_instInhabitedHeaders_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_instInhabitedHeaders_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedHeaders_default___closed__0_value;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__1;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__2;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5;
static lean_once_cell_t l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "indexes"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "validity"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Std_Http_instReprHeaders_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Http_instReprHeaders_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprHeaders_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprHeaders___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprHeaders = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instMembershipNameHeaders;
static const lean_closure_object l_Std_Http_instDecidableMemNameHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instDecidableMemNameHeaders___closed__0 = (const lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__0_value;
static const lean_closure_object l_Std_Http_instDecidableMemNameHeaders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instDecidableMemNameHeaders___closed__1 = (const lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__0 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__1 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__2 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__3 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__4 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__5 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__6 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__0_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__7 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__8 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__9 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Headers_hasEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Headers_hasEntry___closed__0 = (const lean_object*)&l_Std_Http_Headers_hasEntry___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Headers_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Headers_get_x21___closed__0 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__0_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__1 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__1_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__2 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__2_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__3 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__3_value;
static lean_once_cell_t l_Std_Http_Headers_get_x21___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_get_x21___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object*);
static lean_once_cell_t l_Std_Http_Headers_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Headers_empty;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_erase___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__0_value),((lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__1_value)} };
static const lean_object* l_Std_Http_Headers_erase___closed__0 = (const lean_object*)&l_Std_Http_Headers_erase___closed__0_value;
static lean_once_cell_t l_Std_Http_Headers_erase___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_erase___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object*);
static const lean_string_object l_Std_Http_Headers_instToString___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_Headers_instToString___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Headers_instToString___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Headers_instToString___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instToString___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instToString___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instToString___closed__0_value)} };
static const lean_object* l_Std_Http_Headers_instToString___closed__1 = (const lean_object*)&l_Std_Http_Headers_instToString___closed__1_value;
static const lean_closure_object l_Std_Http_Headers_instToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instToString___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instToString___closed__1_value)} };
static const lean_object* l_Std_Http_Headers_instToString___closed__2 = (const lean_object*)&l_Std_Http_Headers_instToString___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instToString = (const lean_object*)&l_Std_Http_Headers_instToString___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instEncodeV11___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instToString___closed__0_value)} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instEncodeV11___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value)} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___closed__1 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instEncodeV11 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEmptyCollection;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object*);
static const lean_closure_object l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instSingletonProdNameValue___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instSingletonProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instSingletonProdNameValue = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instInsertProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instInsertProdNameValue___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instInsertProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instInsertProdNameValue = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instUnion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_merge___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instUnion___closed__0 = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instUnion = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object*, lean_object*);
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_unsigned_to_nat(16u);
v___x_5_ = lean_mk_array(v___x_4_, v___x_3_);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__1, &l_Std_Http_instInhabitedHeaders_default___closed__1_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__1);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__2, &l_Std_Http_instInhabitedHeaders_default___closed__2_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__2);
v___x_10_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__3, &l_Std_Http_instInhabitedHeaders_default___closed__3_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__3);
return v___x_12_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_nat_to_int(v_a_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_dec(v_x_16_);
return v_x_17_;
}
else
{
lean_object* v_head_19_; lean_object* v_tail_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_31_; 
v_head_19_ = lean_ctor_get(v_x_18_, 0);
v_tail_20_ = lean_ctor_get(v_x_18_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_18_);
if (v_isSharedCheck_31_ == 0)
{
v___x_22_ = v_x_18_;
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_tail_20_);
lean_inc(v_head_19_);
lean_dec(v_x_18_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_31_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
lean_inc(v_x_16_);
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 5);
lean_ctor_set(v___x_22_, 1, v_x_16_);
lean_ctor_set(v___x_22_, 0, v_x_17_);
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_x_17_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_x_16_);
v___x_25_ = v_reuseFailAlloc_30_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = l_Nat_reprFast(v_head_19_);
v___x_27_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
v___x_28_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_25_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v_x_17_ = v___x_28_;
v_x_18_ = v_tail_20_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_dec(v_x_32_);
return v_x_33_;
}
else
{
lean_object* v_head_35_; lean_object* v_tail_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_47_; 
v_head_35_ = lean_ctor_get(v_x_34_, 0);
v_tail_36_ = lean_ctor_get(v_x_34_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_47_ == 0)
{
v___x_38_ = v_x_34_;
v_isShared_39_ = v_isSharedCheck_47_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_tail_36_);
lean_inc(v_head_35_);
lean_dec(v_x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_47_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
lean_inc(v_x_32_);
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 5);
lean_ctor_set(v___x_38_, 1, v_x_32_);
lean_ctor_set(v___x_38_, 0, v_x_33_);
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_x_33_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_x_32_);
v___x_41_ = v_reuseFailAlloc_46_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_42_ = l_Nat_reprFast(v_head_35_);
v___x_43_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
v___x_44_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_41_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15_spec__17(v_x_32_, v___x_44_, v_tail_36_);
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(lean_object* v___y_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = l_Nat_reprFast(v___y_48_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v___x_53_; 
lean_dec(v_x_52_);
v___x_53_ = lean_box(0);
return v___x_53_;
}
else
{
lean_object* v_tail_54_; 
v_tail_54_ = lean_ctor_get(v_x_51_, 1);
if (lean_obj_tag(v_tail_54_) == 0)
{
lean_object* v_head_55_; lean_object* v___x_56_; 
lean_dec(v_x_52_);
v_head_55_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_head_55_);
lean_dec_ref(v_x_51_);
v___x_56_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(v_head_55_);
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_inc(v_tail_54_);
v_head_57_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_head_57_);
lean_dec_ref(v_x_51_);
v___x_58_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13___lam__0(v_head_57_);
v___x_59_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13_spec__15(v_x_52_, v___x_58_, v_tail_54_);
return v___x_59_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__0));
v___x_69_ = lean_string_length(v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__5);
v___x_71_ = lean_nat_to_int(v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(lean_object* v_xs_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_array_get_size(v_xs_79_);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_eq(v___x_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_83_ = lean_array_to_list(v_xs_79_);
v___x_84_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_85_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8_spec__13(v___x_83_, v___x_84_);
v___x_86_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6);
v___x_87_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7));
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_85_);
v___x_89_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8));
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_86_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Std_Format_fill(v___x_91_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
lean_dec_ref(v_xs_79_);
v___x_93_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10));
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
lean_dec(v_x_94_);
return v_x_95_;
}
else
{
lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_head_97_ = lean_ctor_get(v_x_96_, 0);
v_tail_98_ = lean_ctor_get(v_x_96_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_107_ == 0)
{
v___x_100_ = v_x_96_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_tail_98_);
lean_inc(v_head_97_);
lean_dec(v_x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
lean_inc(v_x_94_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 5);
lean_ctor_set(v___x_100_, 1, v_x_94_);
lean_ctor_set(v___x_100_, 0, v_x_95_);
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_x_95_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_x_94_);
v___x_103_ = v_reuseFailAlloc_106_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_head_97_);
v_x_95_ = v___x_104_;
v_x_96_ = v_tail_98_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v___x_110_; 
lean_dec(v_x_109_);
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v_tail_111_; 
v_tail_111_ = lean_ctor_get(v_x_108_, 1);
if (lean_obj_tag(v_tail_111_) == 0)
{
lean_object* v_head_112_; 
lean_dec(v_x_109_);
v_head_112_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_head_112_);
lean_dec_ref(v_x_108_);
return v_head_112_;
}
else
{
lean_object* v_head_113_; lean_object* v___x_114_; 
lean_inc(v_tail_111_);
v_head_113_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_head_113_);
lean_dec_ref(v_x_108_);
v___x_114_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__7(v_x_109_, v_head_113_, v_tail_111_);
return v___x_114_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__0));
v___x_118_ = lean_string_length(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__2);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(lean_object* v_x_125_){
_start:
{
lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_149_; 
v_fst_126_ = lean_ctor_get(v_x_125_, 0);
v_snd_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_149_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_149_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_149_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_131_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_126_);
v___x_132_ = lean_box(0);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 1);
lean_ctor_set(v___x_129_, 1, v___x_132_);
lean_ctor_set(v___x_129_, 0, v___x_131_);
v___x_134_ = v___x_129_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_148_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; lean_object* v___x_147_; 
v___x_135_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8(v_snd_127_);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
v___x_137_ = l_List_reverse___redArg(v___x_136_);
v___x_138_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_139_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_137_, v___x_138_);
v___x_140_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_141_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4));
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_139_);
v___x_143_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5));
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_140_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = 0;
v___x_147_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*1, v___x_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_dec(v_x_150_);
return v_x_151_;
}
else
{
lean_object* v_head_153_; lean_object* v_tail_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_164_; 
v_head_153_ = lean_ctor_get(v_x_152_, 0);
v_tail_154_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_164_ == 0)
{
v___x_156_ = v_x_152_;
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_tail_154_);
lean_inc(v_head_153_);
lean_dec(v_x_152_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_164_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
lean_inc(v_x_150_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 5);
lean_ctor_set(v___x_156_, 1, v_x_150_);
lean_ctor_set(v___x_156_, 0, v_x_151_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_x_151_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_x_150_);
v___x_159_ = v_reuseFailAlloc_163_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_153_);
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v_x_151_ = v___x_161_;
v_x_152_ = v_tail_154_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_dec(v_x_165_);
return v_x_166_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_head_168_ = lean_ctor_get(v_x_167_, 0);
v_tail_169_ = lean_ctor_get(v_x_167_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_x_167_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_tail_169_);
lean_inc(v_head_168_);
lean_dec(v_x_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
lean_inc(v_x_165_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 5);
lean_ctor_set(v___x_171_, 1, v_x_165_);
lean_ctor_set(v___x_171_, 0, v_x_166_);
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_x_166_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_x_165_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_168_);
v___x_176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10_spec__16(v_x_165_, v___x_176_, v_tail_169_);
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v___x_182_; 
lean_dec(v_x_181_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v_tail_183_; 
v_tail_183_ = lean_ctor_get(v_x_180_, 1);
if (lean_obj_tag(v_tail_183_) == 0)
{
lean_object* v_head_184_; lean_object* v___x_185_; 
lean_dec(v_x_181_);
v_head_184_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_184_);
lean_dec_ref(v_x_180_);
v___x_185_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_184_);
return v___x_185_;
}
else
{
lean_object* v_head_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc(v_tail_183_);
v_head_186_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_186_);
lean_dec_ref(v_x_180_);
v___x_187_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_head_186_);
v___x_188_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6_spec__10(v_x_181_, v___x_187_, v_tail_183_);
return v___x_188_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__2));
v___x_194_ = lean_string_length(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3, &l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3_once, _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__3);
v___x_196_ = lean_nat_to_int(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(lean_object* v_a_199_){
_start:
{
if (lean_obj_tag(v_a_199_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__1));
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_201_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_202_ = l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__6(v_a_199_, v___x_201_);
v___x_203_ = lean_obj_once(&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4, &l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4_once, _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__4);
v___x_204_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg___closed__5));
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_202_);
v___x_206_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8));
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_203_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_x_211_){
_start:
{
lean_object* v_fst_212_; lean_object* v_snd_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_235_; 
v_fst_212_ = lean_ctor_get(v_x_211_, 0);
v_snd_213_ = lean_ctor_get(v_x_211_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_235_ == 0)
{
v___x_215_ = v_x_211_;
v_isShared_216_ = v_isSharedCheck_235_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_snd_213_);
lean_inc(v_fst_212_);
lean_dec(v_x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_235_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_217_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_212_);
v___x_218_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 1);
lean_ctor_set(v___x_215_, 1, v___x_218_);
lean_ctor_set(v___x_215_, 0, v___x_217_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_234_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_221_ = l_Std_Http_Header_instReprValue_repr___redArg(v_snd_213_);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
v___x_223_ = l_List_reverse___redArg(v___x_222_);
v___x_224_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_225_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_223_, v___x_224_);
v___x_226_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__3);
v___x_227_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__4));
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_225_);
v___x_229_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg___closed__5));
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_226_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = 0;
v___x_233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*1, v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_dec(v_x_236_);
return v_x_237_;
}
else
{
lean_object* v_head_239_; lean_object* v_tail_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_250_; 
v_head_239_ = lean_ctor_get(v_x_238_, 0);
v_tail_240_ = lean_ctor_get(v_x_238_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_x_238_);
if (v_isSharedCheck_250_ == 0)
{
v___x_242_ = v_x_238_;
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_tail_240_);
lean_inc(v_head_239_);
lean_dec(v_x_238_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
lean_inc(v_x_236_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 5);
lean_ctor_set(v___x_242_, 1, v_x_236_);
lean_ctor_set(v___x_242_, 0, v_x_237_);
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_x_237_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_x_236_);
v___x_245_ = v_reuseFailAlloc_249_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_239_);
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v_x_237_ = v___x_247_;
v_x_238_ = v_tail_240_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_dec(v_x_251_);
return v_x_252_;
}
else
{
lean_object* v_head_254_; lean_object* v_tail_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_265_; 
v_head_254_ = lean_ctor_get(v_x_253_, 0);
v_tail_255_ = lean_ctor_get(v_x_253_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_265_ == 0)
{
v___x_257_ = v_x_253_;
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_tail_255_);
lean_inc(v_head_254_);
lean_dec(v_x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
lean_inc(v_x_251_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 5);
lean_ctor_set(v___x_257_, 1, v_x_251_);
lean_ctor_set(v___x_257_, 0, v_x_252_);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_x_252_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_x_251_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_254_);
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__10(v_x_251_, v___x_262_, v_tail_255_);
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_268_; 
lean_dec(v_x_267_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v_tail_269_; 
v_tail_269_ = lean_ctor_get(v_x_266_, 1);
if (lean_obj_tag(v_tail_269_) == 0)
{
lean_object* v_head_270_; lean_object* v___x_271_; 
lean_dec(v_x_267_);
v_head_270_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_head_270_);
lean_dec_ref(v_x_266_);
v___x_271_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_270_);
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
lean_inc(v_tail_269_);
v_head_272_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_head_272_);
lean_dec_ref(v_x_266_);
v___x_273_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_272_);
v___x_274_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(v_x_267_, v___x_273_, v_tail_269_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object* v_xs_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_276_ = lean_array_get_size(v_xs_275_);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_nat_dec_eq(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_279_ = lean_array_to_list(v_xs_275_);
v___x_280_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__3));
v___x_281_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(v___x_279_, v___x_280_);
v___x_282_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__6);
v___x_283_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__7));
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_281_);
v___x_285_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__8));
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_282_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Std_Format_fill(v___x_287_);
return v___x_288_;
}
else
{
lean_object* v___x_289_; 
lean_dec_ref(v_xs_275_);
v___x_289_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__10));
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_inc(v_x_290_);
return v_x_290_;
}
else
{
lean_object* v_key_292_; lean_object* v_value_293_; lean_object* v_tail_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_key_292_ = lean_ctor_get(v_x_291_, 0);
v_value_293_ = lean_ctor_get(v_x_291_, 1);
v_tail_294_ = lean_ctor_get(v_x_291_, 2);
v___x_295_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_x_290_, v_tail_294_);
lean_inc(v_value_293_);
lean_inc(v_key_292_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_key_292_);
lean_ctor_set(v___x_296_, 1, v_value_293_);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___boxed(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_x_298_, v_x_299_);
lean_dec(v_x_299_);
lean_dec(v_x_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(lean_object* v_as_301_, size_t v_i_302_, size_t v_stop_303_, lean_object* v_b_304_){
_start:
{
uint8_t v___x_305_; 
v___x_305_ = lean_usize_dec_eq(v_i_302_, v_stop_303_);
if (v___x_305_ == 0)
{
size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_sub(v_i_302_, v___x_306_);
v___x_308_ = lean_array_uget_borrowed(v_as_301_, v___x_307_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_b_304_, v___x_308_);
lean_dec(v_b_304_);
v_i_302_ = v___x_307_;
v_b_304_ = v___x_309_;
goto _start;
}
else
{
return v_b_304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3___boxed(lean_object* v_as_311_, lean_object* v_i_312_, lean_object* v_stop_313_, lean_object* v_b_314_){
_start:
{
size_t v_i_boxed_315_; size_t v_stop_boxed_316_; lean_object* v_res_317_; 
v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
lean_dec(v_i_312_);
v_stop_boxed_316_ = lean_unbox_usize(v_stop_313_);
lean_dec(v_stop_313_);
v_res_317_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_as_311_, v_i_boxed_315_, v_stop_boxed_316_, v_b_314_);
lean_dec_ref(v_as_311_);
return v_res_317_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(11u);
v___x_332_ = lean_nat_to_int(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6));
v___x_347_ = lean_string_length(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object* v_x_354_){
_start:
{
lean_object* v_indexes_355_; lean_object* v_entries_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_415_; 
v_indexes_355_ = lean_ctor_get(v_x_354_, 1);
v_entries_356_ = lean_ctor_get(v_x_354_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_415_ == 0)
{
v___x_358_ = v_x_354_;
v_isShared_359_ = v_isSharedCheck_415_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_indexes_355_);
lean_inc(v_entries_356_);
lean_dec(v_x_354_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_415_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_buckets_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_413_; 
v_buckets_360_ = lean_ctor_get(v_indexes_355_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_indexes_355_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_indexes_355_, 0);
lean_dec(v_unused_414_);
v___x_362_ = v_indexes_355_;
v_isShared_363_ = v_isSharedCheck_413_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_buckets_360_);
lean_dec(v_indexes_355_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_413_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_364_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4));
v___x_365_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5));
v___x_366_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7);
v___x_367_ = l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(v_entries_356_);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 4);
lean_ctor_set(v___x_362_, 1, v___x_367_);
lean_ctor_set(v___x_362_, 0, v___x_366_);
v___x_369_ = v___x_362_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_412_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = 0;
v___x_371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_370_);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 5);
lean_ctor_set(v___x_358_, 1, v___x_371_);
lean_ctor_set(v___x_358_, 0, v___x_365_);
v___x_373_ = v___x_358_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_411_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___y_384_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_374_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5_spec__8___closed__2));
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_box(1);
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9));
v___x_379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_364_);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11));
v___x_405_ = lean_box(0);
v___x_406_ = lean_array_get_size(v_buckets_360_);
v___x_407_ = lean_nat_dec_lt(v___x_381_, v___x_406_);
if (v___x_407_ == 0)
{
lean_dec_ref(v_buckets_360_);
v___y_384_ = v___x_405_;
goto v___jp_383_;
}
else
{
size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_usize_of_nat(v___x_406_);
v___x_409_ = ((size_t)0ULL);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__3(v_buckets_360_, v___x_408_, v___x_409_, v___x_405_);
lean_dec_ref(v_buckets_360_);
v___y_384_ = v___x_410_;
goto v___jp_383_;
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_385_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v___y_384_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_382_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Repr_addAppParen(v___x_386_, v___x_381_);
v___x_388_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_366_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_370_);
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_380_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_374_);
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_376_);
v___x_393_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13));
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_364_);
v___x_396_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15));
v___x_397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_399_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_397_);
v___x_401_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_398_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*1, v___x_370_);
return v___x_404_;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(7u);
v___x_426_ = lean_nat_to_int(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_428_ = ((lean_object*)(l_Std_Http_instReprHeaders_repr___redArg___closed__3));
v___x_429_ = lean_obj_once(&l_Std_Http_instReprHeaders_repr___redArg___closed__4, &l_Std_Http_instReprHeaders_repr___redArg___closed__4_once, _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4);
v___x_430_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_427_);
v___x_431_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = 0;
v___x_433_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*1, v___x_432_);
v___x_434_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_428_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_436_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_434_);
v___x_438_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_435_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*1, v___x_432_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object* v_x_442_, lean_object* v_prec_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_Http_instReprHeaders_repr___redArg(v_x_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object* v_x_445_, lean_object* v_prec_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Http_instReprHeaders_repr(v_x_445_, v_prec_446_);
lean_dec(v_prec_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object* v_x_448_, lean_object* v_prec_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object* v_x_451_, lean_object* v_prec_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(v_x_451_, v_prec_452_);
lean_dec(v_prec_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(lean_object* v_a_454_, lean_object* v_n_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___redArg(v_a_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(lean_object* v_a_457_, lean_object* v_n_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(v_a_457_, v_n_458_);
lean_dec(v_n_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(v_x_463_, v_x_464_);
lean_dec(v_x_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___redArg(v_x_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5___boxed(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1_spec__5(v_x_469_, v_x_470_);
lean_dec(v_x_470_);
return v_res_471_;
}
}
static lean_object* _init_l_Std_Http_instMembershipNameHeaders(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = lean_box(0);
return v___x_474_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object* v_name_477_, lean_object* v_h_478_){
_start:
{
lean_object* v_indexes_479_; lean_object* v___f_480_; lean_object* v___f_481_; uint8_t v___x_482_; 
v_indexes_479_ = lean_ctor_get(v_h_478_, 1);
v___f_480_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_481_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_480_, v___f_481_, v_indexes_479_, v_name_477_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object* v_name_483_, lean_object* v_h_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Std_Http_instDecidableMemNameHeaders(v_name_483_, v_h_484_);
lean_dec_ref(v_h_484_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object* v_headers_487_, lean_object* v_name_488_){
_start:
{
lean_object* v_entries_489_; lean_object* v_indexes_490_; lean_object* v___f_491_; lean_object* v___f_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_entry_495_; lean_object* v___x_496_; lean_object* v_snd_497_; 
v_entries_489_ = lean_ctor_get(v_headers_487_, 0);
v_indexes_490_ = lean_ctor_get(v_headers_487_, 1);
v___f_491_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_492_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_491_, v___f_492_, v_indexes_490_, v_name_488_);
v___x_494_ = lean_unsigned_to_nat(0u);
v_entry_495_ = lean_array_fget(v___x_493_, v___x_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_array_fget_borrowed(v_entries_489_, v_entry_495_);
lean_dec(v_entry_495_);
v_snd_497_ = lean_ctor_get(v___x_496_, 1);
lean_inc(v_snd_497_);
return v_snd_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object* v_headers_498_, lean_object* v_name_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Http_Headers_get___redArg(v_headers_498_, v_name_499_);
lean_dec_ref(v_headers_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object* v_headers_501_, lean_object* v_name_502_, lean_object* v_h_503_){
_start:
{
lean_object* v_entries_504_; lean_object* v_indexes_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_entry_510_; lean_object* v___x_511_; lean_object* v_snd_512_; 
v_entries_504_ = lean_ctor_get(v_headers_501_, 0);
v_indexes_505_ = lean_ctor_get(v_headers_501_, 1);
v___f_506_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_507_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_506_, v___f_507_, v_indexes_505_, v_name_502_);
v___x_509_ = lean_unsigned_to_nat(0u);
v_entry_510_ = lean_array_fget(v___x_508_, v___x_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_array_fget_borrowed(v_entries_504_, v_entry_510_);
lean_dec(v_entry_510_);
v_snd_512_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_snd_512_);
return v_snd_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object* v_headers_513_, lean_object* v_name_514_, lean_object* v_h_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_Http_Headers_get(v_headers_513_, v_name_514_, v_h_515_);
lean_dec_ref(v_headers_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object* v___x_517_, lean_object* v_entries_518_, lean_object* v_x1_519_, lean_object* v_x2_520_, lean_object* v_x3_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_snd_524_; 
v___x_522_ = lean_array_fget_borrowed(v___x_517_, v_x1_519_);
v___x_523_ = lean_array_fget_borrowed(v_entries_518_, v___x_522_);
v_snd_524_ = lean_ctor_get(v___x_523_, 1);
lean_inc(v_snd_524_);
return v_snd_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object* v___x_525_, lean_object* v_entries_526_, lean_object* v_x1_527_, lean_object* v_x2_528_, lean_object* v_x3_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Http_Headers_getAll___redArg___lam__0(v___x_525_, v_entries_526_, v_x1_527_, v_x2_528_, v_x3_529_);
lean_dec(v_x2_528_);
lean_dec(v_x1_527_);
lean_dec_ref(v_entries_526_);
lean_dec_ref(v___x_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object* v_headers_550_, lean_object* v_name_551_){
_start:
{
lean_object* v_entries_552_; lean_object* v_indexes_553_; lean_object* v___f_554_; lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___f_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_entries_562_; 
v_entries_552_ = lean_ctor_get(v_headers_550_, 0);
lean_inc_ref(v_entries_552_);
v_indexes_553_ = lean_ctor_get(v_headers_550_, 1);
lean_inc_ref(v_indexes_553_);
lean_dec_ref(v_headers_550_);
v___f_554_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_555_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_554_, v___f_555_, v_indexes_553_, v_name_551_);
lean_dec_ref(v_indexes_553_);
lean_inc(v___x_556_);
v___f_557_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_557_, 0, v___x_556_);
lean_closure_set(v___f_557_, 1, v_entries_552_);
v___x_558_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_559_ = lean_array_get_size(v___x_556_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_mk_empty_array_with_capacity(v___x_559_);
v_entries_562_ = l_Array_mapFinIdxM_map___redArg(v___x_558_, v___x_556_, v___f_557_, v___x_559_, v___x_560_, v___x_561_);
return v_entries_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object* v_headers_563_, lean_object* v_name_564_, lean_object* v_h_565_){
_start:
{
lean_object* v_entries_566_; lean_object* v_indexes_567_; lean_object* v___f_568_; lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_entries_576_; 
v_entries_566_ = lean_ctor_get(v_headers_563_, 0);
lean_inc_ref(v_entries_566_);
v_indexes_567_ = lean_ctor_get(v_headers_563_, 1);
lean_inc_ref(v_indexes_567_);
lean_dec_ref(v_headers_563_);
v___f_568_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_569_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_568_, v___f_569_, v_indexes_567_, v_name_564_);
lean_dec_ref(v_indexes_567_);
lean_inc(v___x_570_);
v___f_571_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_571_, 0, v___x_570_);
lean_closure_set(v___f_571_, 1, v_entries_566_);
v___x_572_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_573_ = lean_array_get_size(v___x_570_);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_573_);
v_entries_576_ = l_Array_mapFinIdxM_map___redArg(v___x_572_, v___x_570_, v___f_571_, v___x_573_, v___x_574_, v___x_575_);
return v_entries_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object* v_headers_577_, lean_object* v_name_578_){
_start:
{
lean_object* v___f_579_; lean_object* v___f_580_; uint8_t v___x_581_; 
v___f_579_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_580_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_578_);
v___x_581_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_579_, v___f_580_, v_name_578_, v_headers_577_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v_name_578_);
lean_dec_ref(v_headers_577_);
v___x_582_ = lean_box(0);
return v___x_582_;
}
else
{
lean_object* v_entries_583_; lean_object* v_indexes_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_entries_591_; lean_object* v___x_592_; 
v_entries_583_ = lean_ctor_get(v_headers_577_, 0);
lean_inc_ref(v_entries_583_);
v_indexes_584_ = lean_ctor_get(v_headers_577_, 1);
lean_inc_ref(v_indexes_584_);
lean_dec_ref(v_headers_577_);
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_579_, v___f_580_, v_indexes_584_, v_name_578_);
lean_dec_ref(v_indexes_584_);
lean_inc(v___x_585_);
v___f_586_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_586_, 0, v___x_585_);
lean_closure_set(v___f_586_, 1, v_entries_583_);
v___x_587_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_588_ = lean_array_get_size(v___x_585_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_mk_empty_array_with_capacity(v___x_588_);
v_entries_591_ = l_Array_mapFinIdxM_map___redArg(v___x_587_, v___x_585_, v___f_586_, v___x_588_, v___x_589_, v___x_590_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_entries_591_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object* v_headers_593_, lean_object* v_name_594_){
_start:
{
lean_object* v___f_595_; lean_object* v___f_596_; uint8_t v___x_597_; 
v___f_595_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_596_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_594_);
v___x_597_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_595_, v___f_596_, v_name_594_, v_headers_593_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec_ref(v_name_594_);
v___x_598_ = lean_box(0);
return v___x_598_;
}
else
{
lean_object* v_entries_599_; lean_object* v_indexes_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_entry_603_; lean_object* v___x_604_; lean_object* v_snd_605_; lean_object* v___x_606_; 
v_entries_599_ = lean_ctor_get(v_headers_593_, 0);
v_indexes_600_ = lean_ctor_get(v_headers_593_, 1);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_595_, v___f_596_, v_indexes_600_, v_name_594_);
v___x_602_ = lean_unsigned_to_nat(0u);
v_entry_603_ = lean_array_fget(v___x_601_, v___x_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_array_fget_borrowed(v_entries_599_, v_entry_603_);
lean_dec(v_entry_603_);
v_snd_605_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_snd_605_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_snd_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object* v_headers_607_, lean_object* v_name_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Http_Headers_get_x3f(v_headers_607_, v_name_608_);
lean_dec_ref(v_headers_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object* v_value_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_a_613_, lean_object* v_x_614_, lean_object* v___y_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = l_Std_Http_Header_instBEqValue_beq(v_a_613_, v_value_610_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v_a_613_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_611_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v___x_611_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_a_613_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_612_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object* v_value_622_, lean_object* v___x_623_, lean_object* v___x_624_, lean_object* v_a_625_, lean_object* v_x_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_Http_Headers_hasEntry___lam__1(v_value_622_, v___x_623_, v___x_624_, v_a_625_, v_x_626_, v___y_627_);
lean_dec_ref(v___y_627_);
lean_dec_ref(v_value_622_);
return v_res_628_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object* v_headers_632_, lean_object* v_name_633_, lean_object* v_value_634_){
_start:
{
lean_object* v___f_635_; lean_object* v___f_636_; uint8_t v___x_637_; 
v___f_635_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_636_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_633_);
v___x_637_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_635_, v___f_636_, v_name_633_, v_headers_632_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_value_634_);
lean_dec_ref(v_name_633_);
lean_dec_ref(v_headers_632_);
return v___x_637_;
}
else
{
lean_object* v_entries_638_; lean_object* v_indexes_639_; lean_object* v___x_640_; lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_entries_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___f_649_; size_t v_sz_650_; size_t v___x_651_; lean_object* v___x_652_; lean_object* v_fst_653_; 
v_entries_638_ = lean_ctor_get(v_headers_632_, 0);
lean_inc_ref(v_entries_638_);
v_indexes_639_ = lean_ctor_get(v_headers_632_, 1);
lean_inc_ref(v_indexes_639_);
lean_dec_ref(v_headers_632_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_635_, v___f_636_, v_indexes_639_, v_name_633_);
lean_dec_ref(v_indexes_639_);
lean_inc(v___x_640_);
v___f_641_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_641_, 0, v___x_640_);
lean_closure_set(v___f_641_, 1, v_entries_638_);
v___x_642_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_643_ = lean_array_get_size(v___x_640_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_mk_empty_array_with_capacity(v___x_643_);
v_entries_646_ = l_Array_mapFinIdxM_map___redArg(v___x_642_, v___x_640_, v___f_641_, v___x_643_, v___x_644_, v___x_645_);
v___x_647_ = lean_box(0);
v___x_648_ = ((lean_object*)(l_Std_Http_Headers_hasEntry___closed__0));
v___f_649_ = lean_alloc_closure((void*)(l_Std_Http_Headers_hasEntry___lam__1___boxed), 6, 3);
lean_closure_set(v___f_649_, 0, v_value_634_);
lean_closure_set(v___f_649_, 1, v___x_648_);
lean_closure_set(v___f_649_, 2, v___x_647_);
v_sz_650_ = lean_array_size(v_entries_646_);
v___x_651_ = ((size_t)0ULL);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_642_, v_entries_646_, v___f_649_, v_sz_650_, v___x_651_, v___x_648_);
v_fst_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_fst_653_);
lean_dec(v___x_652_);
if (lean_obj_tag(v_fst_653_) == 0)
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
else
{
lean_object* v_val_655_; 
v_val_655_ = lean_ctor_get(v_fst_653_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v_fst_653_);
if (lean_obj_tag(v_val_655_) == 0)
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
else
{
lean_dec_ref(v_val_655_);
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object* v_headers_657_, lean_object* v_name_658_, lean_object* v_value_659_){
_start:
{
uint8_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_Std_Http_Headers_hasEntry(v_headers_657_, v_name_658_, v_value_659_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object* v_headers_662_, lean_object* v_name_663_){
_start:
{
lean_object* v___f_664_; lean_object* v___f_665_; uint8_t v___x_666_; 
v___f_664_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_665_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_663_);
v___x_666_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_664_, v___f_665_, v_name_663_, v_headers_662_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_name_663_);
lean_dec_ref(v_headers_662_);
v___x_667_ = lean_box(0);
return v___x_667_;
}
else
{
lean_object* v_entries_668_; lean_object* v_indexes_669_; lean_object* v___x_670_; lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_entries_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_entries_668_ = lean_ctor_get(v_headers_662_, 0);
lean_inc_ref(v_entries_668_);
v_indexes_669_ = lean_ctor_get(v_headers_662_, 1);
lean_inc_ref(v_indexes_669_);
lean_dec_ref(v_headers_662_);
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_664_, v___f_665_, v_indexes_669_, v_name_663_);
lean_dec_ref(v_indexes_669_);
lean_inc(v___x_670_);
v___f_671_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_671_, 0, v___x_670_);
lean_closure_set(v___f_671_, 1, v_entries_668_);
v___x_672_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_673_ = lean_array_get_size(v___x_670_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_mk_empty_array_with_capacity(v___x_673_);
v_entries_676_ = l_Array_mapFinIdxM_map___redArg(v___x_672_, v___x_670_, v___f_671_, v___x_673_, v___x_674_, v___x_675_);
v___x_677_ = lean_array_get_size(v_entries_676_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_sub(v___x_677_, v___x_678_);
v___x_680_ = lean_nat_dec_lt(v___x_679_, v___x_677_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_dec(v___x_679_);
lean_dec(v_entries_676_);
v___x_681_ = lean_box(0);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_array_fget(v_entries_676_, v___x_679_);
lean_dec(v___x_679_);
lean_dec(v_entries_676_);
v___x_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object* v_headers_684_, lean_object* v_name_685_, lean_object* v_d_686_){
_start:
{
lean_object* v___f_687_; lean_object* v___f_688_; uint8_t v___x_689_; 
v___f_687_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_688_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_685_);
v___x_689_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_687_, v___f_688_, v_name_685_, v_headers_684_);
if (v___x_689_ == 0)
{
lean_dec_ref(v_name_685_);
lean_inc_ref(v_d_686_);
return v_d_686_;
}
else
{
lean_object* v_entries_690_; lean_object* v_indexes_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_entry_694_; lean_object* v___x_695_; lean_object* v_snd_696_; 
v_entries_690_ = lean_ctor_get(v_headers_684_, 0);
v_indexes_691_ = lean_ctor_get(v_headers_684_, 1);
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_687_, v___f_688_, v_indexes_691_, v_name_685_);
v___x_693_ = lean_unsigned_to_nat(0u);
v_entry_694_ = lean_array_fget(v___x_692_, v___x_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_array_fget_borrowed(v_entries_690_, v_entry_694_);
lean_dec(v_entry_694_);
v_snd_696_ = lean_ctor_get(v___x_695_, 1);
lean_inc(v_snd_696_);
return v_snd_696_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object* v_headers_697_, lean_object* v_name_698_, lean_object* v_d_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_Http_Headers_getD(v_headers_697_, v_name_698_, v_d_699_);
lean_dec_ref(v_d_699_);
lean_dec_ref(v_headers_697_);
return v_res_700_;
}
}
static lean_object* _init_l_Std_Http_Headers_get_x21___closed__4(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_705_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__3));
v___x_706_ = lean_unsigned_to_nat(14u);
v___x_707_ = lean_unsigned_to_nat(22u);
v___x_708_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__2));
v___x_709_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__1));
v___x_710_ = l_mkPanicMessageWithDecl(v___x_709_, v___x_708_, v___x_707_, v___x_706_, v___x_705_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object* v_headers_711_, lean_object* v_name_712_){
_start:
{
lean_object* v___f_713_; lean_object* v___f_714_; uint8_t v___x_715_; 
v___f_713_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_714_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_712_);
v___x_715_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_713_, v___f_714_, v_name_712_, v_headers_711_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec_ref(v_name_712_);
v___x_716_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___x_717_ = lean_obj_once(&l_Std_Http_Headers_get_x21___closed__4, &l_Std_Http_Headers_get_x21___closed__4_once, _init_l_Std_Http_Headers_get_x21___closed__4);
v___x_718_ = l_panic___redArg(v___x_716_, v___x_717_);
return v___x_718_;
}
else
{
lean_object* v_entries_719_; lean_object* v_indexes_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_entry_723_; lean_object* v___x_724_; lean_object* v_snd_725_; 
v_entries_719_ = lean_ctor_get(v_headers_711_, 0);
v_indexes_720_ = lean_ctor_get(v_headers_711_, 1);
v___x_721_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_713_, v___f_714_, v_indexes_720_, v_name_712_);
v___x_722_ = lean_unsigned_to_nat(0u);
v_entry_723_ = lean_array_fget(v___x_721_, v___x_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_array_fget_borrowed(v_entries_719_, v_entry_723_);
lean_dec(v_entry_723_);
v_snd_725_ = lean_ctor_get(v___x_724_, 1);
lean_inc(v_snd_725_);
return v_snd_725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object* v_headers_726_, lean_object* v_name_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_Http_Headers_get_x21(v_headers_726_, v_name_727_);
lean_dec_ref(v_headers_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object* v_i_729_, lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_mk_empty_array_with_capacity(v___x_731_);
v___x_733_ = lean_array_push(v___x_732_, v_i_729_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
else
{
lean_object* v_val_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v_val_735_ = lean_ctor_get(v_x_730_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v_x_730_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v_x_730_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_val_735_);
lean_dec(v_x_730_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_array_push(v_val_735_, v_i_729_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object* v_headers_744_, lean_object* v_key_745_, lean_object* v_value_746_){
_start:
{
lean_object* v_entries_747_; lean_object* v_indexes_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_762_; 
v_entries_747_ = lean_ctor_get(v_headers_744_, 0);
v_indexes_748_ = lean_ctor_get(v_headers_744_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_headers_744_);
if (v_isSharedCheck_762_ == 0)
{
v___x_750_ = v_headers_744_;
v_isShared_751_ = v_isSharedCheck_762_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_indexes_748_);
lean_inc(v_entries_747_);
lean_dec(v_headers_744_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_762_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v_i_754_; lean_object* v_f_755_; lean_object* v___x_756_; lean_object* v_entries_757_; lean_object* v_indexes_758_; lean_object* v___x_760_; 
v___f_752_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_753_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_754_ = lean_array_get_size(v_entries_747_);
v_f_755_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_755_, 0, v_i_754_);
lean_inc_ref(v_key_745_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_key_745_);
lean_ctor_set(v___x_756_, 1, v_value_746_);
v_entries_757_ = lean_array_push(v_entries_747_, v___x_756_);
v_indexes_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_752_, v___f_753_, v_indexes_748_, v_key_745_, v_f_755_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v_indexes_758_);
lean_ctor_set(v___x_750_, 0, v_entries_757_);
v___x_760_ = v___x_750_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_entries_757_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_indexes_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object* v_headers_763_, lean_object* v_name_764_, lean_object* v_value_765_){
_start:
{
lean_object* v_entries_766_; lean_object* v_indexes_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_783_; 
v_entries_766_ = lean_ctor_get(v_headers_763_, 0);
v_indexes_767_ = lean_ctor_get(v_headers_763_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_headers_763_);
if (v_isSharedCheck_783_ == 0)
{
v___x_769_ = v_headers_763_;
v_isShared_770_ = v_isSharedCheck_783_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_indexes_767_);
lean_inc(v_entries_766_);
lean_dec(v_headers_763_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_783_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v_i_775_; lean_object* v_f_776_; lean_object* v___x_777_; lean_object* v_entries_778_; lean_object* v_indexes_779_; lean_object* v___x_781_; 
v___x_771_ = l_Std_Http_Header_Name_ofString_x21(v_name_764_);
v___x_772_ = l_Std_Http_Header_Value_ofString_x21(v_value_765_);
v___f_773_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_774_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_775_ = lean_array_get_size(v_entries_766_);
v_f_776_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_776_, 0, v_i_775_);
lean_inc_ref(v___x_771_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_771_);
lean_ctor_set(v___x_777_, 1, v___x_772_);
v_entries_778_ = lean_array_push(v_entries_766_, v___x_777_);
v_indexes_779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_773_, v___f_774_, v_indexes_767_, v___x_771_, v_f_776_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_indexes_779_);
lean_ctor_set(v___x_769_, 0, v_entries_778_);
v___x_781_ = v___x_769_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_entries_778_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_indexes_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object* v_headers_784_, lean_object* v_name_785_, lean_object* v_value_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_Http_Header_Name_ofString_x3f(v_name_785_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_788_; 
lean_dec_ref(v_value_786_);
lean_dec_ref(v_headers_784_);
v___x_788_ = lean_box(0);
return v___x_788_;
}
else
{
lean_object* v_val_789_; lean_object* v___x_790_; 
v_val_789_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_val_789_);
lean_dec_ref(v___x_787_);
v___x_790_ = l_Std_Http_Header_Value_ofString_x3f(v_value_786_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; 
lean_dec(v_val_789_);
lean_dec_ref(v_headers_784_);
v___x_791_ = lean_box(0);
return v___x_791_;
}
else
{
lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_815_; 
v_val_792_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_815_ == 0)
{
v___x_794_ = v___x_790_;
v_isShared_795_ = v_isSharedCheck_815_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_dec(v___x_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_815_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_entries_796_; lean_object* v_indexes_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_814_; 
v_entries_796_ = lean_ctor_get(v_headers_784_, 0);
v_indexes_797_ = lean_ctor_get(v_headers_784_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_headers_784_);
if (v_isSharedCheck_814_ == 0)
{
v___x_799_ = v_headers_784_;
v_isShared_800_ = v_isSharedCheck_814_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_indexes_797_);
lean_inc(v_entries_796_);
lean_dec(v_headers_784_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_814_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v_i_803_; lean_object* v_f_804_; lean_object* v___x_805_; lean_object* v_entries_806_; lean_object* v_indexes_807_; lean_object* v___x_809_; 
v___f_801_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_802_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_803_ = lean_array_get_size(v_entries_796_);
v_f_804_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_804_, 0, v_i_803_);
lean_inc(v_val_789_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v_val_789_);
lean_ctor_set(v___x_805_, 1, v_val_792_);
v_entries_806_ = lean_array_push(v_entries_796_, v___x_805_);
v_indexes_807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_801_, v___f_802_, v_indexes_797_, v_val_789_, v_f_804_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_indexes_807_);
lean_ctor_set(v___x_799_, 0, v_entries_806_);
v___x_809_ = v___x_799_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_entries_806_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_indexes_807_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_809_);
v___x_811_ = v___x_794_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object* v_key_816_, lean_object* v___f_817_, lean_object* v___f_818_, lean_object* v_x1_819_, lean_object* v_x2_820_){
_start:
{
lean_object* v_entries_821_; lean_object* v_indexes_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_834_; 
v_entries_821_ = lean_ctor_get(v_x1_819_, 0);
v_indexes_822_ = lean_ctor_get(v_x1_819_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_x1_819_);
if (v_isSharedCheck_834_ == 0)
{
v___x_824_ = v_x1_819_;
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_indexes_822_);
lean_inc(v_entries_821_);
lean_dec(v_x1_819_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_i_826_; lean_object* v_f_827_; lean_object* v___x_828_; lean_object* v_entries_829_; lean_object* v_indexes_830_; lean_object* v___x_832_; 
v_i_826_ = lean_array_get_size(v_entries_821_);
v_f_827_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_827_, 0, v_i_826_);
lean_inc_ref(v_key_816_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_key_816_);
lean_ctor_set(v___x_828_, 1, v_x2_820_);
v_entries_829_ = lean_array_push(v_entries_821_, v___x_828_);
v_indexes_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_817_, v___f_818_, v_indexes_822_, v_key_816_, v_f_827_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v_indexes_830_);
lean_ctor_set(v___x_824_, 0, v_entries_829_);
v___x_832_ = v___x_824_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_entries_829_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_indexes_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object* v_headers_835_, lean_object* v_key_836_, lean_object* v_values_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_array_get_size(v_values_837_);
v___x_840_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_841_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
if (v___x_841_ == 0)
{
lean_dec_ref(v_values_837_);
lean_dec_ref(v_key_836_);
return v_headers_835_;
}
else
{
lean_object* v___f_842_; lean_object* v___f_843_; lean_object* v___f_844_; uint8_t v___x_845_; 
v___f_842_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_843_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_844_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insertMany___lam__1), 5, 3);
lean_closure_set(v___f_844_, 0, v_key_836_);
lean_closure_set(v___f_844_, 1, v___f_842_);
lean_closure_set(v___f_844_, 2, v___f_843_);
v___x_845_ = lean_nat_dec_le(v___x_839_, v___x_839_);
if (v___x_845_ == 0)
{
if (v___x_841_ == 0)
{
lean_dec_ref(v___f_844_);
lean_dec_ref(v_values_837_);
return v_headers_835_;
}
else
{
size_t v___x_846_; size_t v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((size_t)0ULL);
v___x_847_ = lean_usize_of_nat(v___x_839_);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_840_, v___f_844_, v_values_837_, v___x_846_, v___x_847_, v_headers_835_);
return v___x_848_;
}
}
else
{
size_t v___x_849_; size_t v___x_850_; lean_object* v___x_851_; 
v___x_849_ = ((size_t)0ULL);
v___x_850_ = lean_usize_of_nat(v___x_839_);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_840_, v___f_844_, v_values_837_, v___x_849_, v___x_850_, v_headers_835_);
return v___x_851_;
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__2, &l_Std_Http_instInhabitedHeaders_default___closed__2_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__2);
v___x_855_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0));
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object* v_00_u03b2_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1);
return v___x_858_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty___closed__0(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_859_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty(void){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(lean_object* v_i_861_, lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_val_866_; lean_object* v___x_867_; 
v___x_864_ = lean_box(0);
v___x_865_ = l_Std_Http_Headers_insert___lam__0(v_i_861_, v___x_864_);
v_val_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_val_866_);
lean_dec(v___x_865_);
v___x_867_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_867_, 0, v_a_862_);
lean_ctor_set(v___x_867_, 1, v_val_866_);
lean_ctor_set(v___x_867_, 2, v_x_863_);
return v___x_867_;
}
else
{
lean_object* v_key_868_; lean_object* v_value_869_; lean_object* v_tail_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_885_; 
v_key_868_ = lean_ctor_get(v_x_863_, 0);
v_value_869_ = lean_ctor_get(v_x_863_, 1);
v_tail_870_ = lean_ctor_get(v_x_863_, 2);
v_isSharedCheck_885_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_885_ == 0)
{
v___x_872_ = v_x_863_;
v_isShared_873_ = v_isSharedCheck_885_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_tail_870_);
lean_inc(v_value_869_);
lean_inc(v_key_868_);
lean_dec(v_x_863_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_885_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; 
v___x_874_ = lean_string_dec_eq(v_key_868_, v_a_862_);
if (v___x_874_ == 0)
{
lean_object* v_tail_875_; lean_object* v___x_877_; 
v_tail_875_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_861_, v_a_862_, v_tail_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 2, v_tail_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_key_868_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_value_869_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_tail_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_val_881_; lean_object* v___x_883_; 
lean_dec(v_key_868_);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v_value_869_);
v___x_880_ = l_Std_Http_Headers_insert___lam__0(v_i_861_, v___x_879_);
v_val_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_881_);
lean_dec(v___x_880_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v_val_881_);
lean_ctor_set(v___x_872_, 0, v_a_862_);
v___x_883_ = v___x_872_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_862_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_val_881_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_tail_870_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
return v_x_886_;
}
else
{
lean_object* v_key_888_; lean_object* v_value_889_; lean_object* v_tail_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_913_; 
v_key_888_ = lean_ctor_get(v_x_887_, 0);
v_value_889_ = lean_ctor_get(v_x_887_, 1);
v_tail_890_ = lean_ctor_get(v_x_887_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_913_ == 0)
{
v___x_892_ = v_x_887_;
v_isShared_893_ = v_isSharedCheck_913_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_tail_890_);
lean_inc(v_value_889_);
lean_inc(v_key_888_);
lean_dec(v_x_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_913_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v_fold_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_894_ = lean_array_get_size(v_x_886_);
v___x_895_ = lean_string_hash(v_key_888_);
v___x_896_ = 32ULL;
v___x_897_ = lean_uint64_shift_right(v___x_895_, v___x_896_);
v_fold_898_ = lean_uint64_xor(v___x_895_, v___x_897_);
v___x_899_ = 16ULL;
v___x_900_ = lean_uint64_shift_right(v_fold_898_, v___x_899_);
v___x_901_ = lean_uint64_xor(v_fold_898_, v___x_900_);
v___x_902_ = lean_uint64_to_usize(v___x_901_);
v___x_903_ = lean_usize_of_nat(v___x_894_);
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_sub(v___x_903_, v___x_904_);
v___x_906_ = lean_usize_land(v___x_902_, v___x_905_);
v___x_907_ = lean_array_uget_borrowed(v_x_886_, v___x_906_);
lean_inc(v___x_907_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 2, v___x_907_);
v___x_909_ = v___x_892_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_key_888_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_value_889_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v___x_907_);
v___x_909_ = v_reuseFailAlloc_912_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; 
v___x_910_ = lean_array_uset(v_x_886_, v___x_906_, v___x_909_);
v_x_886_ = v___x_910_;
v_x_887_ = v_tail_890_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_i_914_, lean_object* v_source_915_, lean_object* v_target_916_){
_start:
{
lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_917_ = lean_array_get_size(v_source_915_);
v___x_918_ = lean_nat_dec_lt(v_i_914_, v___x_917_);
if (v___x_918_ == 0)
{
lean_dec_ref(v_source_915_);
lean_dec(v_i_914_);
return v_target_916_;
}
else
{
lean_object* v_es_919_; lean_object* v___x_920_; lean_object* v_source_921_; lean_object* v_target_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_es_919_ = lean_array_fget(v_source_915_, v_i_914_);
v___x_920_ = lean_box(0);
v_source_921_ = lean_array_fset(v_source_915_, v_i_914_, v___x_920_);
v_target_922_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_916_, v_es_919_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_add(v_i_914_, v___x_923_);
lean_dec(v_i_914_);
v_i_914_ = v___x_924_;
v_source_915_ = v_source_921_;
v_target_916_ = v_target_922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(lean_object* v_data_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_nbuckets_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_927_ = lean_array_get_size(v_data_926_);
v___x_928_ = lean_unsigned_to_nat(2u);
v_nbuckets_929_ = lean_nat_mul(v___x_927_, v___x_928_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_box(0);
v___x_932_ = lean_mk_array(v_nbuckets_929_, v___x_931_);
v___x_933_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v___x_930_, v_data_926_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object* v_a_934_, lean_object* v_x_935_){
_start:
{
if (lean_obj_tag(v_x_935_) == 0)
{
uint8_t v___x_936_; 
v___x_936_ = 0;
return v___x_936_;
}
else
{
lean_object* v_key_937_; lean_object* v_tail_938_; uint8_t v___x_939_; 
v_key_937_ = lean_ctor_get(v_x_935_, 0);
v_tail_938_ = lean_ctor_get(v_x_935_, 2);
v___x_939_ = lean_string_dec_eq(v_key_937_, v_a_934_);
if (v___x_939_ == 0)
{
v_x_935_ = v_tail_938_;
goto _start;
}
else
{
return v___x_939_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_941_, lean_object* v_x_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_941_, v_x_942_);
lean_dec(v_x_942_);
lean_dec_ref(v_a_941_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object* v_i_945_, lean_object* v_m_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_size_948_; lean_object* v_buckets_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_999_; 
v_size_948_ = lean_ctor_get(v_m_946_, 0);
v_buckets_949_ = lean_ctor_get(v_m_946_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_m_946_);
if (v_isSharedCheck_999_ == 0)
{
v___x_951_ = v_m_946_;
v_isShared_952_ = v_isSharedCheck_999_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_buckets_949_);
lean_inc(v_size_948_);
lean_dec(v_m_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_999_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v___x_956_; uint64_t v_fold_957_; uint64_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; lean_object* v_bkt_966_; uint8_t v___x_967_; 
v___x_953_ = lean_array_get_size(v_buckets_949_);
v___x_954_ = lean_string_hash(v_a_947_);
v___x_955_ = 32ULL;
v___x_956_ = lean_uint64_shift_right(v___x_954_, v___x_955_);
v_fold_957_ = lean_uint64_xor(v___x_954_, v___x_956_);
v___x_958_ = 16ULL;
v___x_959_ = lean_uint64_shift_right(v_fold_957_, v___x_958_);
v___x_960_ = lean_uint64_xor(v_fold_957_, v___x_959_);
v___x_961_ = lean_uint64_to_usize(v___x_960_);
v___x_962_ = lean_usize_of_nat(v___x_953_);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_sub(v___x_962_, v___x_963_);
v___x_965_ = lean_usize_land(v___x_961_, v___x_964_);
v_bkt_966_ = lean_array_uget_borrowed(v_buckets_949_, v___x_965_);
v___x_967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_947_, v_bkt_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_size_x27_971_; lean_object* v___x_972_; lean_object* v_buckets_x27_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_970_ = lean_array_push(v___x_969_, v_i_945_);
v_size_x27_971_ = lean_nat_add(v_size_948_, v___x_968_);
lean_dec(v_size_948_);
lean_inc(v_bkt_966_);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v_a_947_);
lean_ctor_set(v___x_972_, 1, v___x_970_);
lean_ctor_set(v___x_972_, 2, v_bkt_966_);
v_buckets_x27_973_ = lean_array_uset(v_buckets_949_, v___x_965_, v___x_972_);
v___x_974_ = lean_unsigned_to_nat(4u);
v___x_975_ = lean_nat_mul(v_size_x27_971_, v___x_974_);
v___x_976_ = lean_unsigned_to_nat(3u);
v___x_977_ = lean_nat_div(v___x_975_, v___x_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_array_get_size(v_buckets_x27_973_);
v___x_979_ = lean_nat_dec_le(v___x_977_, v___x_978_);
lean_dec(v___x_977_);
if (v___x_979_ == 0)
{
lean_object* v_val_980_; lean_object* v___x_982_; 
v_val_980_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_buckets_x27_973_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_val_980_);
lean_ctor_set(v___x_951_, 0, v_size_x27_971_);
v___x_982_ = v___x_951_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_size_x27_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_val_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_985_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_buckets_x27_973_);
lean_ctor_set(v___x_951_, 0, v_size_x27_971_);
v___x_985_ = v___x_951_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_size_x27_971_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_buckets_x27_973_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v___x_987_; lean_object* v_buckets_x27_988_; lean_object* v_bkt_x27_989_; lean_object* v___y_991_; uint8_t v___x_996_; 
lean_inc(v_bkt_966_);
v___x_987_ = lean_box(0);
v_buckets_x27_988_ = lean_array_uset(v_buckets_949_, v___x_965_, v___x_987_);
lean_inc_ref(v_a_947_);
v_bkt_x27_989_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__3(v_i_945_, v_a_947_, v_bkt_966_);
v___x_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_947_, v_bkt_x27_989_);
lean_dec_ref(v_a_947_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_sub(v_size_948_, v___x_997_);
lean_dec(v_size_948_);
v___y_991_ = v___x_998_;
goto v___jp_990_;
}
else
{
v___y_991_ = v_size_948_;
goto v___jp_990_;
}
v___jp_990_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = lean_array_uset(v_buckets_x27_988_, v___x_965_, v_bkt_x27_989_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v___x_992_);
lean_ctor_set(v___x_951_, 0, v___y_991_);
v___x_994_ = v___x_951_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___y_991_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
if (lean_obj_tag(v_x_1001_) == 0)
{
return v_x_1000_;
}
else
{
lean_object* v_head_1002_; lean_object* v_tail_1003_; lean_object* v_fst_1004_; lean_object* v_entries_1005_; lean_object* v_indexes_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1017_; 
v_head_1002_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_head_1002_);
v_tail_1003_ = lean_ctor_get(v_x_1001_, 1);
lean_inc(v_tail_1003_);
lean_dec_ref(v_x_1001_);
v_fst_1004_ = lean_ctor_get(v_head_1002_, 0);
lean_inc(v_fst_1004_);
v_entries_1005_ = lean_ctor_get(v_x_1000_, 0);
v_indexes_1006_ = lean_ctor_get(v_x_1000_, 1);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_x_1000_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1008_ = v_x_1000_;
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_indexes_1006_);
lean_inc(v_entries_1005_);
lean_dec(v_x_1000_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_i_1010_; lean_object* v_entries_1011_; lean_object* v_indexes_1012_; lean_object* v___x_1014_; 
v_i_1010_ = lean_array_get_size(v_entries_1005_);
v_entries_1011_ = lean_array_push(v_entries_1005_, v_head_1002_);
v_indexes_1012_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1010_, v_indexes_1006_, v_fst_1004_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v_indexes_1012_);
lean_ctor_set(v___x_1008_, 0, v_entries_1011_);
v___x_1014_ = v___x_1008_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_entries_1011_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_indexes_1012_);
v___x_1014_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
v_x_1000_ = v___x_1014_;
v_x_1001_ = v_tail_1003_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object* v_pairs_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0, &l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once, _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0);
v___x_1021_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v___x_1020_, v_pairs_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object* v_pairs_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object* v_00_u03b2_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_pairs_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object* v_00_u03b2_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_x_1030_, v_x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1033_, lean_object* v_a_1034_, lean_object* v_x_1035_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_a_1034_, v_x_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1037_, lean_object* v_a_1038_, lean_object* v_x_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(v_00_u03b2_1037_, v_a_1038_, v_x_1039_);
lean_dec(v_x_1039_);
lean_dec_ref(v_a_1038_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1042_, lean_object* v_data_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2___redArg(v_data_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1045_, lean_object* v_i_1046_, lean_object* v_source_1047_, lean_object* v_target_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3___redArg(v_i_1046_, v_source_1047_, v_target_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_1051_, v_x_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object* v_headers_1054_, lean_object* v_name_1055_){
_start:
{
lean_object* v_indexes_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; uint8_t v___x_1059_; 
v_indexes_1056_ = lean_ctor_get(v_headers_1054_, 1);
v___f_1057_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1058_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1057_, v___f_1058_, v_indexes_1056_, v_name_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object* v_headers_1060_, lean_object* v_name_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Std_Http_Headers_contains(v_headers_1060_, v_name_1061_);
lean_dec_ref(v_headers_1060_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object* v___f_1064_, lean_object* v___f_1065_, lean_object* v_x1_1066_, lean_object* v_x2_1067_){
_start:
{
lean_object* v_fst_1068_; lean_object* v_entries_1069_; lean_object* v_indexes_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1081_; 
v_fst_1068_ = lean_ctor_get(v_x2_1067_, 0);
lean_inc(v_fst_1068_);
v_entries_1069_ = lean_ctor_get(v_x1_1066_, 0);
v_indexes_1070_ = lean_ctor_get(v_x1_1066_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x1_1066_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1072_ = v_x1_1066_;
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_indexes_1070_);
lean_inc(v_entries_1069_);
lean_dec(v_x1_1066_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_i_1074_; lean_object* v_f_1075_; lean_object* v_entries_1076_; lean_object* v_indexes_1077_; lean_object* v___x_1079_; 
v_i_1074_ = lean_array_get_size(v_entries_1069_);
v_f_1075_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1075_, 0, v_i_1074_);
v_entries_1076_ = lean_array_push(v_entries_1069_, v_x2_1067_);
v_indexes_1077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1064_, v___f_1065_, v_indexes_1070_, v_fst_1068_, v_f_1075_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v_indexes_1077_);
lean_ctor_set(v___x_1072_, 0, v_entries_1076_);
v___x_1079_ = v___x_1072_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_entries_1076_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_indexes_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0(lean_object* v_name_1082_, lean_object* v_x1_1083_, lean_object* v_x2_1084_){
_start:
{
lean_object* v_fst_1085_; uint8_t v___x_1086_; 
v_fst_1085_ = lean_ctor_get(v_x2_1084_, 0);
v___x_1086_ = lean_string_dec_eq(v_fst_1085_, v_name_1082_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_array_push(v_x1_1083_, v_x2_1084_);
return v___x_1087_;
}
else
{
lean_dec_ref(v_x2_1084_);
return v_x1_1083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__0___boxed(lean_object* v_name_1088_, lean_object* v_x1_1089_, lean_object* v_x2_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_Http_Headers_erase___lam__0(v_name_1088_, v_x1_1089_, v_x2_1090_);
lean_dec_ref(v_name_1088_);
return v_res_1091_;
}
}
static lean_object* _init_l_Std_Http_Headers_erase___closed__1(void){
_start:
{
lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; 
v___f_1095_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_1096_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_1097_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1096_, v___f_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object* v_headers_1098_, lean_object* v_name_1099_){
_start:
{
lean_object* v___f_1100_; lean_object* v___f_1101_; uint8_t v___x_1102_; 
v___f_1100_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1101_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1099_);
v___x_1102_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1100_, v___f_1101_, v_name_1099_, v_headers_1098_);
if (v___x_1102_ == 0)
{
lean_dec_ref(v_name_1099_);
return v_headers_1098_;
}
else
{
lean_object* v_entries_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_entries_1103_ = lean_ctor_get(v_headers_1098_, 0);
lean_inc_ref(v_entries_1103_);
lean_dec_ref(v_headers_1098_);
v___f_1104_ = ((lean_object*)(l_Std_Http_Headers_erase___closed__0));
v___x_1105_ = lean_obj_once(&l_Std_Http_Headers_erase___closed__1, &l_Std_Http_Headers_erase___closed__1_once, _init_l_Std_Http_Headers_erase___closed__1);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1119_ = lean_array_get_size(v_entries_1103_);
v___x_1120_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_1121_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1122_ = lean_nat_dec_lt(v___x_1106_, v___x_1119_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v_entries_1103_);
lean_dec_ref(v_name_1099_);
v___y_1108_ = v___x_1120_;
goto v___jp_1107_;
}
else
{
lean_object* v___f_1123_; uint8_t v___x_1124_; 
v___f_1123_ = lean_alloc_closure((void*)(l_Std_Http_Headers_erase___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1123_, 0, v_name_1099_);
v___x_1124_ = lean_nat_dec_le(v___x_1119_, v___x_1119_);
if (v___x_1124_ == 0)
{
if (v___x_1122_ == 0)
{
lean_dec_ref(v___f_1123_);
lean_dec_ref(v_entries_1103_);
v___y_1108_ = v___x_1120_;
goto v___jp_1107_;
}
else
{
size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = lean_usize_of_nat(v___x_1119_);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1121_, v___f_1123_, v_entries_1103_, v___x_1125_, v___x_1126_, v___x_1120_);
v___y_1108_ = v___x_1127_;
goto v___jp_1107_;
}
}
else
{
size_t v___x_1128_; size_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = lean_usize_of_nat(v___x_1119_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1121_, v___f_1123_, v_entries_1103_, v___x_1128_, v___x_1129_, v___x_1120_);
v___y_1108_ = v___x_1130_;
goto v___jp_1107_;
}
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = lean_array_get_size(v___y_1108_);
v___x_1110_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1111_ = lean_nat_dec_lt(v___x_1106_, v___x_1109_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v___y_1108_);
return v___x_1105_;
}
else
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_nat_dec_le(v___x_1109_, v___x_1109_);
if (v___x_1112_ == 0)
{
if (v___x_1111_ == 0)
{
lean_dec_ref(v___y_1108_);
return v___x_1105_;
}
else
{
size_t v___x_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = lean_usize_of_nat(v___x_1109_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1110_, v___f_1104_, v___y_1108_, v___x_1113_, v___x_1114_, v___x_1105_);
return v___x_1115_;
}
}
else
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((size_t)0ULL);
v___x_1117_ = lean_usize_of_nat(v___x_1109_);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1110_, v___f_1104_, v___y_1108_, v___x_1116_, v___x_1117_, v___x_1105_);
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object* v_headers_1131_){
_start:
{
lean_object* v_entries_1132_; lean_object* v___x_1133_; 
v_entries_1132_ = lean_ctor_get(v_headers_1131_, 0);
v___x_1133_ = lean_array_get_size(v_entries_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object* v_headers_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_Http_Headers_size(v_headers_1134_);
lean_dec_ref(v_headers_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object* v_headers_1136_){
_start:
{
lean_object* v_entries_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_entries_1137_ = lean_ctor_get(v_headers_1136_, 0);
v___x_1138_ = lean_array_get_size(v_entries_1137_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_nat_dec_eq(v___x_1138_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object* v_headers_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_Std_Http_Headers_isEmpty(v_headers_1141_);
lean_dec_ref(v_headers_1141_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object* v_as_1144_, size_t v_i_1145_, size_t v_stop_1146_, lean_object* v_b_1147_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_eq(v_i_1145_, v_stop_1146_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v_fst_1150_; lean_object* v_entries_1151_; lean_object* v_indexes_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1165_; 
v___x_1149_ = lean_array_uget_borrowed(v_as_1144_, v_i_1145_);
v_fst_1150_ = lean_ctor_get(v___x_1149_, 0);
v_entries_1151_ = lean_ctor_get(v_b_1147_, 0);
v_indexes_1152_ = lean_ctor_get(v_b_1147_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_b_1147_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1154_ = v_b_1147_;
v_isShared_1155_ = v_isSharedCheck_1165_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_indexes_1152_);
lean_inc(v_entries_1151_);
lean_dec(v_b_1147_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1165_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_i_1156_; lean_object* v_entries_1157_; lean_object* v_indexes_1158_; lean_object* v___x_1160_; 
v_i_1156_ = lean_array_get_size(v_entries_1151_);
lean_inc(v___x_1149_);
v_entries_1157_ = lean_array_push(v_entries_1151_, v___x_1149_);
lean_inc(v_fst_1150_);
v_indexes_1158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1156_, v_indexes_1152_, v_fst_1150_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_indexes_1158_);
lean_ctor_set(v___x_1154_, 0, v_entries_1157_);
v___x_1160_ = v___x_1154_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_entries_1157_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_indexes_1158_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
size_t v___x_1161_; size_t v___x_1162_; 
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_add(v_i_1145_, v___x_1161_);
v_i_1145_ = v___x_1162_;
v_b_1147_ = v___x_1160_;
goto _start;
}
}
}
else
{
return v_b_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object* v_as_1166_, lean_object* v_i_1167_, lean_object* v_stop_1168_, lean_object* v_b_1169_){
_start:
{
size_t v_i_boxed_1170_; size_t v_stop_boxed_1171_; lean_object* v_res_1172_; 
v_i_boxed_1170_ = lean_unbox_usize(v_i_1167_);
lean_dec(v_i_1167_);
v_stop_boxed_1171_ = lean_unbox_usize(v_stop_1168_);
lean_dec(v_stop_1168_);
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1166_, v_i_boxed_1170_, v_stop_boxed_1171_, v_b_1169_);
lean_dec_ref(v_as_1166_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object* v_m1_1173_, lean_object* v_m2_1174_){
_start:
{
lean_object* v_entries_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_entries_1175_ = lean_ctor_get(v_m2_1174_, 0);
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_array_get_size(v_entries_1175_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
return v_m1_1173_;
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_nat_dec_le(v___x_1177_, v___x_1177_);
if (v___x_1179_ == 0)
{
if (v___x_1178_ == 0)
{
return v_m1_1173_;
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1177_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1175_, v___x_1180_, v___x_1181_, v_m1_1173_);
return v___x_1182_;
}
}
else
{
size_t v___x_1183_; size_t v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = ((size_t)0ULL);
v___x_1184_ = lean_usize_of_nat(v___x_1177_);
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1175_, v___x_1183_, v___x_1184_, v_m1_1173_);
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object* v_m1_1186_, lean_object* v_m2_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1186_, v_m2_1187_);
lean_dec_ref(v_m2_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object* v_headers1_1189_, lean_object* v_headers2_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_headers1_1189_, v_headers2_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object* v_headers1_1192_, lean_object* v_headers2_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_Http_Headers_merge(v_headers1_1192_, v_headers2_1193_);
lean_dec_ref(v_headers2_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object* v_00_u03b2_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_m1_1198_, lean_object* v_m2_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1198_, v_m2_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object* v_00_u03b2_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_m1_1204_, lean_object* v_m2_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(v_00_u03b2_1201_, v_inst_1202_, v_inst_1203_, v_m1_1204_, v_m2_1205_);
lean_dec_ref(v_m2_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object* v_00_u03b2_1207_, lean_object* v_as_1208_, size_t v_i_1209_, size_t v_stop_1210_, lean_object* v_b_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1208_, v_i_1209_, v_stop_1210_, v_b_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1213_, lean_object* v_as_1214_, lean_object* v_i_1215_, lean_object* v_stop_1216_, lean_object* v_b_1217_){
_start:
{
size_t v_i_boxed_1218_; size_t v_stop_boxed_1219_; lean_object* v_res_1220_; 
v_i_boxed_1218_ = lean_unbox_usize(v_i_1215_);
lean_dec(v_i_1215_);
v_stop_boxed_1219_ = lean_unbox_usize(v_stop_1216_);
lean_dec(v_stop_1216_);
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(v_00_u03b2_1213_, v_as_1214_, v_i_boxed_1218_, v_stop_boxed_1219_, v_b_1217_);
lean_dec_ref(v_as_1214_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object* v_map_1221_){
_start:
{
lean_object* v_entries_1222_; lean_object* v___x_1223_; 
v_entries_1222_ = lean_ctor_get(v_map_1221_, 0);
lean_inc_ref(v_entries_1222_);
lean_dec_ref(v_map_1221_);
v___x_1223_ = lean_array_to_list(v_entries_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object* v_00_u03b2_1224_, lean_object* v_map_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_map_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object* v_headers_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_headers_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object* v_headers_1229_){
_start:
{
lean_object* v_entries_1230_; 
v_entries_1230_ = lean_ctor_get(v_headers_1229_, 0);
lean_inc_ref(v_entries_1230_);
return v_entries_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object* v_headers_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_Http_Headers_toArray(v_headers_1231_);
lean_dec_ref(v_headers_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object* v_f_1233_, lean_object* v_as_1234_, size_t v_i_1235_, size_t v_stop_1236_, lean_object* v_b_1237_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_eq(v_i_1235_, v_stop_1236_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; 
v___x_1239_ = lean_array_uget_borrowed(v_as_1234_, v_i_1235_);
v_fst_1240_ = lean_ctor_get(v___x_1239_, 0);
v_snd_1241_ = lean_ctor_get(v___x_1239_, 1);
lean_inc(v_f_1233_);
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
v___x_1242_ = lean_apply_3(v_f_1233_, v_b_1237_, v_fst_1240_, v_snd_1241_);
v___x_1243_ = ((size_t)1ULL);
v___x_1244_ = lean_usize_add(v_i_1235_, v___x_1243_);
v_i_1235_ = v___x_1244_;
v_b_1237_ = v___x_1242_;
goto _start;
}
else
{
lean_dec(v_f_1233_);
return v_b_1237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object* v_f_1246_, lean_object* v_as_1247_, lean_object* v_i_1248_, lean_object* v_stop_1249_, lean_object* v_b_1250_){
_start:
{
size_t v_i_boxed_1251_; size_t v_stop_boxed_1252_; lean_object* v_res_1253_; 
v_i_boxed_1251_ = lean_unbox_usize(v_i_1248_);
lean_dec(v_i_1248_);
v_stop_boxed_1252_ = lean_unbox_usize(v_stop_1249_);
lean_dec(v_stop_1249_);
v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1246_, v_as_1247_, v_i_boxed_1251_, v_stop_boxed_1252_, v_b_1250_);
lean_dec_ref(v_as_1247_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object* v_headers_1254_, lean_object* v_init_1255_, lean_object* v_f_1256_){
_start:
{
lean_object* v_entries_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_entries_1257_ = lean_ctor_get(v_headers_1254_, 0);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_array_get_size(v_entries_1257_);
v___x_1260_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_dec(v_f_1256_);
return v_init_1255_;
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_nat_dec_le(v___x_1259_, v___x_1259_);
if (v___x_1261_ == 0)
{
if (v___x_1260_ == 0)
{
lean_dec(v_f_1256_);
return v_init_1255_;
}
else
{
size_t v___x_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = ((size_t)0ULL);
v___x_1263_ = lean_usize_of_nat(v___x_1259_);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1256_, v_entries_1257_, v___x_1262_, v___x_1263_, v_init_1255_);
return v___x_1264_;
}
}
else
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((size_t)0ULL);
v___x_1266_ = lean_usize_of_nat(v___x_1259_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1256_, v_entries_1257_, v___x_1265_, v___x_1266_, v_init_1255_);
return v___x_1267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object* v_headers_1268_, lean_object* v_init_1269_, lean_object* v_f_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Std_Http_Headers_fold___redArg(v_headers_1268_, v_init_1269_, v_f_1270_);
lean_dec_ref(v_headers_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object* v_00_u03b1_1272_, lean_object* v_headers_1273_, lean_object* v_init_1274_, lean_object* v_f_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_Http_Headers_fold___redArg(v_headers_1273_, v_init_1274_, v_f_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_headers_1278_, lean_object* v_init_1279_, lean_object* v_f_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_Http_Headers_fold(v_00_u03b1_1277_, v_headers_1278_, v_init_1279_, v_f_1280_);
lean_dec_ref(v_headers_1278_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object* v_00_u03b1_1282_, lean_object* v_f_1283_, lean_object* v_as_1284_, size_t v_i_1285_, size_t v_stop_1286_, lean_object* v_b_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1283_, v_as_1284_, v_i_1285_, v_stop_1286_, v_b_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_f_1290_, lean_object* v_as_1291_, lean_object* v_i_1292_, lean_object* v_stop_1293_, lean_object* v_b_1294_){
_start:
{
size_t v_i_boxed_1295_; size_t v_stop_boxed_1296_; lean_object* v_res_1297_; 
v_i_boxed_1295_ = lean_unbox_usize(v_i_1292_);
lean_dec(v_i_1292_);
v_stop_boxed_1296_ = lean_unbox_usize(v_stop_1293_);
lean_dec(v_stop_1293_);
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(v_00_u03b1_1289_, v_f_1290_, v_as_1291_, v_i_boxed_1295_, v_stop_boxed_1296_, v_b_1294_);
lean_dec_ref(v_as_1291_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object* v_f_1298_, size_t v_sz_1299_, size_t v_i_1300_, lean_object* v_bs_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v_f_1298_);
return v_bs_1301_;
}
else
{
lean_object* v_v_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1319_; 
v_v_1303_ = lean_array_uget(v_bs_1301_, v_i_1300_);
v_fst_1304_ = lean_ctor_get(v_v_1303_, 0);
v_snd_1305_ = lean_ctor_get(v_v_1303_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_v_1303_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1307_ = v_v_1303_;
v_isShared_1308_ = v_isSharedCheck_1319_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snd_1305_);
lean_inc(v_fst_1304_);
lean_dec(v_v_1303_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1319_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v_bs_x27_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1309_ = lean_unsigned_to_nat(0u);
v_bs_x27_1310_ = lean_array_uset(v_bs_1301_, v_i_1300_, v___x_1309_);
lean_inc_ref(v_f_1298_);
lean_inc(v_fst_1304_);
v___x_1311_ = lean_apply_2(v_f_1298_, v_fst_1304_, v_snd_1305_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1311_);
v___x_1313_ = v___x_1307_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_fst_1304_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_add(v_i_1300_, v___x_1314_);
v___x_1316_ = lean_array_uset(v_bs_x27_1310_, v_i_1300_, v___x_1313_);
v_i_1300_ = v___x_1315_;
v_bs_1301_ = v___x_1316_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object* v_f_1320_, lean_object* v_sz_1321_, lean_object* v_i_1322_, lean_object* v_bs_1323_){
_start:
{
size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1321_);
lean_dec(v_sz_1321_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1322_);
lean_dec(v_i_1322_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1320_, v_sz_boxed_1324_, v_i_boxed_1325_, v_bs_1323_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object* v_as_1327_, size_t v_i_1328_, size_t v_stop_1329_, lean_object* v_b_1330_){
_start:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_usize_dec_eq(v_i_1328_, v_stop_1329_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v_fst_1333_; lean_object* v_entries_1334_; lean_object* v_indexes_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1348_; 
v___x_1332_ = lean_array_uget_borrowed(v_as_1327_, v_i_1328_);
v_fst_1333_ = lean_ctor_get(v___x_1332_, 0);
v_entries_1334_ = lean_ctor_get(v_b_1330_, 0);
v_indexes_1335_ = lean_ctor_get(v_b_1330_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_b_1330_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1337_ = v_b_1330_;
v_isShared_1338_ = v_isSharedCheck_1348_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_indexes_1335_);
lean_inc(v_entries_1334_);
lean_dec(v_b_1330_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1348_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_i_1339_; lean_object* v_entries_1340_; lean_object* v_indexes_1341_; lean_object* v___x_1343_; 
v_i_1339_ = lean_array_get_size(v_entries_1334_);
lean_inc(v___x_1332_);
v_entries_1340_ = lean_array_push(v_entries_1334_, v___x_1332_);
lean_inc(v_fst_1333_);
v_indexes_1341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1339_, v_indexes_1335_, v_fst_1333_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v_indexes_1341_);
lean_ctor_set(v___x_1337_, 0, v_entries_1340_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_entries_1340_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_indexes_1341_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
size_t v___x_1344_; size_t v___x_1345_; 
v___x_1344_ = ((size_t)1ULL);
v___x_1345_ = lean_usize_add(v_i_1328_, v___x_1344_);
v_i_1328_ = v___x_1345_;
v_b_1330_ = v___x_1343_;
goto _start;
}
}
}
else
{
return v_b_1330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object* v_as_1349_, lean_object* v_i_1350_, lean_object* v_stop_1351_, lean_object* v_b_1352_){
_start:
{
size_t v_i_boxed_1353_; size_t v_stop_boxed_1354_; lean_object* v_res_1355_; 
v_i_boxed_1353_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_stop_boxed_1354_ = lean_unbox_usize(v_stop_1351_);
lean_dec(v_stop_1351_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_1349_, v_i_boxed_1353_, v_stop_boxed_1354_, v_b_1352_);
lean_dec_ref(v_as_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object* v_headers_1356_, lean_object* v_f_1357_){
_start:
{
lean_object* v_entries_1358_; size_t v_sz_1359_; size_t v___x_1360_; lean_object* v_pairs_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_entries_1358_ = lean_ctor_get(v_headers_1356_, 0);
lean_inc_ref(v_entries_1358_);
lean_dec_ref(v_headers_1356_);
v_sz_1359_ = lean_array_size(v_entries_1358_);
v___x_1360_ = ((size_t)0ULL);
v_pairs_1361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_1357_, v_sz_1359_, v___x_1360_, v_entries_1358_);
v___x_1362_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_array_get_size(v_pairs_1361_);
v___x_1365_ = lean_nat_dec_lt(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v_pairs_1361_);
return v___x_1362_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_nat_dec_le(v___x_1364_, v___x_1364_);
if (v___x_1366_ == 0)
{
if (v___x_1365_ == 0)
{
lean_dec_ref(v_pairs_1361_);
return v___x_1362_;
}
else
{
size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_usize_of_nat(v___x_1364_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1361_, v___x_1360_, v___x_1367_, v___x_1362_);
lean_dec_ref(v_pairs_1361_);
return v___x_1368_;
}
}
else
{
size_t v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_usize_of_nat(v___x_1364_);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1361_, v___x_1360_, v___x_1369_, v___x_1362_);
lean_dec_ref(v_pairs_1361_);
return v___x_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object* v_f_1371_, lean_object* v_as_1372_, size_t v_i_1373_, size_t v_stop_1374_, lean_object* v_b_1375_){
_start:
{
lean_object* v___y_1377_; uint8_t v___x_1381_; 
v___x_1381_ = lean_usize_dec_eq(v_i_1373_, v_stop_1374_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v_fst_1383_; lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v___x_1382_ = lean_array_uget(v_as_1372_, v_i_1373_);
v_fst_1383_ = lean_ctor_get(v___x_1382_, 0);
v_snd_1384_ = lean_ctor_get(v___x_1382_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v___x_1382_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_inc(v_fst_1383_);
lean_dec(v___x_1382_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; 
lean_inc_ref(v_f_1371_);
lean_inc(v_fst_1383_);
v___x_1388_ = lean_apply_2(v_f_1371_, v_fst_1383_, v_snd_1384_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_del_object(v___x_1386_);
lean_dec(v_fst_1383_);
v___y_1377_ = v_b_1375_;
goto v___jp_1376_;
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1391_; 
v_val_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_val_1389_);
lean_dec_ref(v___x_1388_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_val_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_fst_1383_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_val_1389_);
v___x_1391_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_array_push(v_b_1375_, v___x_1391_);
v___y_1377_ = v___x_1392_;
goto v___jp_1376_;
}
}
}
}
else
{
lean_dec_ref(v_f_1371_);
return v_b_1375_;
}
v___jp_1376_:
{
size_t v___x_1378_; size_t v___x_1379_; 
v___x_1378_ = ((size_t)1ULL);
v___x_1379_ = lean_usize_add(v_i_1373_, v___x_1378_);
v_i_1373_ = v___x_1379_;
v_b_1375_ = v___y_1377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object* v_f_1395_, lean_object* v_as_1396_, lean_object* v_i_1397_, lean_object* v_stop_1398_, lean_object* v_b_1399_){
_start:
{
size_t v_i_boxed_1400_; size_t v_stop_boxed_1401_; lean_object* v_res_1402_; 
v_i_boxed_1400_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_stop_boxed_1401_ = lean_unbox_usize(v_stop_1398_);
lean_dec(v_stop_1398_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1395_, v_as_1396_, v_i_boxed_1400_, v_stop_boxed_1401_, v_b_1399_);
lean_dec_ref(v_as_1396_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object* v_f_1403_, lean_object* v_as_1404_, lean_object* v_start_1405_, lean_object* v_stop_1406_){
_start:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_1408_ = lean_nat_dec_lt(v_start_1405_, v_stop_1406_);
if (v___x_1408_ == 0)
{
lean_dec_ref(v_f_1403_);
return v___x_1407_;
}
else
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_array_get_size(v_as_1404_);
v___x_1410_ = lean_nat_dec_le(v_stop_1406_, v___x_1409_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_nat_dec_lt(v_start_1405_, v___x_1409_);
if (v___x_1411_ == 0)
{
lean_dec_ref(v_f_1403_);
return v___x_1407_;
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_usize_of_nat(v_start_1405_);
v___x_1413_ = lean_usize_of_nat(v___x_1409_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1403_, v_as_1404_, v___x_1412_, v___x_1413_, v___x_1407_);
return v___x_1414_;
}
}
else
{
size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_usize_of_nat(v_start_1405_);
v___x_1416_ = lean_usize_of_nat(v_stop_1406_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_1403_, v_as_1404_, v___x_1415_, v___x_1416_, v___x_1407_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object* v_f_1418_, lean_object* v_as_1419_, lean_object* v_start_1420_, lean_object* v_stop_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1418_, v_as_1419_, v_start_1420_, v_stop_1421_);
lean_dec(v_stop_1421_);
lean_dec(v_start_1420_);
lean_dec_ref(v_as_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object* v_headers_1423_, lean_object* v_f_1424_){
_start:
{
lean_object* v_entries_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v_pairs_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_entries_1425_ = lean_ctor_get(v_headers_1423_, 0);
v___x_1426_ = lean_unsigned_to_nat(0u);
v___x_1427_ = lean_array_get_size(v_entries_1425_);
v_pairs_1428_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_1424_, v_entries_1425_, v___x_1426_, v___x_1427_);
v___x_1429_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1430_ = lean_array_get_size(v_pairs_1428_);
v___x_1431_ = lean_nat_dec_lt(v___x_1426_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v_pairs_1428_);
return v___x_1429_;
}
else
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_nat_dec_le(v___x_1430_, v___x_1430_);
if (v___x_1432_ == 0)
{
if (v___x_1431_ == 0)
{
lean_dec_ref(v_pairs_1428_);
return v___x_1429_;
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1430_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1428_, v___x_1433_, v___x_1434_, v___x_1429_);
lean_dec_ref(v_pairs_1428_);
return v___x_1435_;
}
}
else
{
size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = lean_usize_of_nat(v___x_1430_);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_1428_, v___x_1436_, v___x_1437_, v___x_1429_);
lean_dec_ref(v_pairs_1428_);
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object* v_headers_1439_, lean_object* v_f_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_Http_Headers_filterMap(v_headers_1439_, v_f_1440_);
lean_dec_ref(v_headers_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object* v_f_1442_, lean_object* v_k_1443_, lean_object* v_v_1444_){
_start:
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
lean_inc_ref(v_v_1444_);
v___x_1445_ = lean_apply_2(v_f_1442_, v_k_1443_, v_v_1444_);
v___x_1446_ = lean_unbox(v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref(v_v_1444_);
v___x_1447_ = lean_box(0);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_v_1444_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object* v_headers_1449_, lean_object* v_f_1450_){
_start:
{
lean_object* v___f_1451_; lean_object* v___x_1452_; 
v___f_1451_ = lean_alloc_closure((void*)(l_Std_Http_Headers_filter___lam__0), 3, 1);
lean_closure_set(v___f_1451_, 0, v_f_1450_);
v___x_1452_ = l_Std_Http_Headers_filterMap(v_headers_1449_, v___f_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object* v_headers_1453_, lean_object* v_f_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_Http_Headers_filter(v_headers_1453_, v_f_1454_);
lean_dec_ref(v_headers_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object* v_name_1456_, lean_object* v_f_1457_, lean_object* v_as_1458_, size_t v_i_1459_, size_t v_stop_1460_, lean_object* v_b_1461_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_eq(v_i_1459_, v_stop_1460_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v_fst_1464_; lean_object* v_snd_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1491_; 
v___x_1463_ = lean_array_uget(v_as_1458_, v_i_1459_);
v_fst_1464_ = lean_ctor_get(v___x_1463_, 0);
v_snd_1465_ = lean_ctor_get(v___x_1463_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1467_ = v___x_1463_;
v_isShared_1468_ = v_isSharedCheck_1491_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snd_1465_);
lean_inc(v_fst_1464_);
lean_dec(v___x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1491_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___y_1470_; uint8_t v___x_1489_; 
v___x_1489_ = lean_string_dec_eq(v_fst_1464_, v_name_1456_);
if (v___x_1489_ == 0)
{
v___y_1470_ = v_snd_1465_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1490_; 
lean_inc_ref(v_f_1457_);
v___x_1490_ = lean_apply_1(v_f_1457_, v_snd_1465_);
v___y_1470_ = v___x_1490_;
goto v___jp_1469_;
}
v___jp_1469_:
{
lean_object* v_entries_1471_; lean_object* v_indexes_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1488_; 
v_entries_1471_ = lean_ctor_get(v_b_1461_, 0);
v_indexes_1472_ = lean_ctor_get(v_b_1461_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_b_1461_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1474_ = v_b_1461_;
v_isShared_1475_ = v_isSharedCheck_1488_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_indexes_1472_);
lean_inc(v_entries_1471_);
lean_dec(v_b_1461_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1488_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_i_1476_; lean_object* v___x_1478_; 
v_i_1476_ = lean_array_get_size(v_entries_1471_);
lean_inc(v_fst_1464_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v___y_1470_);
v___x_1478_ = v___x_1467_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_fst_1464_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___y_1470_);
v___x_1478_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v_entries_1479_; lean_object* v_indexes_1480_; lean_object* v___x_1482_; 
v_entries_1479_ = lean_array_push(v_entries_1471_, v___x_1478_);
v_indexes_1480_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_i_1476_, v_indexes_1472_, v_fst_1464_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v_indexes_1480_);
lean_ctor_set(v___x_1474_, 0, v_entries_1479_);
v___x_1482_ = v___x_1474_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_entries_1479_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_indexes_1480_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
size_t v___x_1483_; size_t v___x_1484_; 
v___x_1483_ = ((size_t)1ULL);
v___x_1484_ = lean_usize_add(v_i_1459_, v___x_1483_);
v_i_1459_ = v___x_1484_;
v_b_1461_ = v___x_1482_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec_ref(v_f_1457_);
return v_b_1461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object* v_name_1492_, lean_object* v_f_1493_, lean_object* v_as_1494_, lean_object* v_i_1495_, lean_object* v_stop_1496_, lean_object* v_b_1497_){
_start:
{
size_t v_i_boxed_1498_; size_t v_stop_boxed_1499_; lean_object* v_res_1500_; 
v_i_boxed_1498_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_stop_boxed_1499_ = lean_unbox_usize(v_stop_1496_);
lean_dec(v_stop_1496_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1492_, v_f_1493_, v_as_1494_, v_i_boxed_1498_, v_stop_boxed_1499_, v_b_1497_);
lean_dec_ref(v_as_1494_);
lean_dec_ref(v_name_1492_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object* v_headers_1501_, lean_object* v_name_1502_, lean_object* v_f_1503_){
_start:
{
lean_object* v___f_1504_; lean_object* v___f_1505_; uint8_t v___x_1506_; 
v___f_1504_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1505_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1502_);
v___x_1506_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1504_, v___f_1505_, v_name_1502_, v_headers_1501_);
if (v___x_1506_ == 0)
{
lean_dec_ref(v_f_1503_);
lean_dec_ref(v_name_1502_);
lean_inc_ref(v_headers_1501_);
return v_headers_1501_;
}
else
{
lean_object* v_entries_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_entries_1507_ = lean_ctor_get(v_headers_1501_, 0);
v___x_1508_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_1509_ = lean_unsigned_to_nat(0u);
v___x_1510_ = lean_array_get_size(v_entries_1507_);
v___x_1511_ = lean_nat_dec_lt(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_dec_ref(v_f_1503_);
lean_dec_ref(v_name_1502_);
return v___x_1508_;
}
else
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_le(v___x_1510_, v___x_1510_);
if (v___x_1512_ == 0)
{
if (v___x_1511_ == 0)
{
lean_dec_ref(v_f_1503_);
lean_dec_ref(v_name_1502_);
return v___x_1508_;
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_of_nat(v___x_1510_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1502_, v_f_1503_, v_entries_1507_, v___x_1513_, v___x_1514_, v___x_1508_);
lean_dec_ref(v_name_1502_);
return v___x_1515_;
}
}
else
{
size_t v___x_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = lean_usize_of_nat(v___x_1510_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_1502_, v_f_1503_, v_entries_1507_, v___x_1516_, v___x_1517_, v___x_1508_);
lean_dec_ref(v_name_1502_);
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object* v_headers_1519_, lean_object* v_name_1520_, lean_object* v_f_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Std_Http_Headers_update(v_headers_1519_, v_name_1520_, v_f_1521_);
lean_dec_ref(v_headers_1519_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object* v_headers_1523_, lean_object* v_name_1524_, lean_object* v_value_1525_){
_start:
{
lean_object* v___f_1526_; lean_object* v___f_1527_; uint8_t v___x_1528_; 
v___f_1526_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1527_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1524_);
v___x_1528_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1526_, v___f_1527_, v_name_1524_, v_headers_1523_);
if (v___x_1528_ == 0)
{
lean_dec_ref(v_value_1525_);
lean_dec_ref(v_name_1524_);
return v_headers_1523_;
}
else
{
lean_object* v_entries_1529_; lean_object* v_indexes_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1544_; 
v_entries_1529_ = lean_ctor_get(v_headers_1523_, 0);
v_indexes_1530_ = lean_ctor_get(v_headers_1523_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_headers_1523_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1532_ = v_headers_1523_;
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_indexes_1530_);
lean_inc(v_entries_1529_);
lean_dec(v_headers_1523_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v_idxs_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_lastIdx_1538_; lean_object* v___x_1539_; lean_object* v_entries_1540_; lean_object* v___x_1542_; 
lean_inc_ref(v_name_1524_);
v_idxs_1534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_1526_, v___f_1527_, v_indexes_1530_, v_name_1524_);
v___x_1535_ = lean_array_get_size(v_idxs_1534_);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_sub(v___x_1535_, v___x_1536_);
v_lastIdx_1538_ = lean_array_fget(v_idxs_1534_, v___x_1537_);
lean_dec(v___x_1537_);
lean_dec(v_idxs_1534_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_name_1524_);
lean_ctor_set(v___x_1539_, 1, v_value_1525_);
v_entries_1540_ = lean_array_fset(v_entries_1529_, v_lastIdx_1538_, v___x_1539_);
lean_dec(v_lastIdx_1538_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v_entries_1540_);
v___x_1542_ = v___x_1532_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_entries_1540_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_indexes_1530_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object* v_x_1545_){
_start:
{
lean_object* v___x_1546_; uint32_t v___x_1547_; uint32_t v___x_1548_; uint8_t v___x_1549_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_string_utf8_get(v_x_1545_, v___x_1546_);
v___x_1548_ = 97;
v___x_1549_ = lean_uint32_dec_le(v___x_1548_, v___x_1547_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_string_utf8_set(v_x_1545_, v___x_1546_, v___x_1547_);
return v___x_1550_;
}
else
{
uint32_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1551_ = 122;
v___x_1552_ = lean_uint32_dec_le(v___x_1547_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_string_utf8_set(v_x_1545_, v___x_1546_, v___x_1547_);
return v___x_1553_;
}
else
{
uint32_t v___x_1554_; uint32_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = 4294967264;
v___x_1555_ = lean_uint32_add(v___x_1547_, v___x_1554_);
v___x_1556_ = lean_string_utf8_set(v_x_1545_, v___x_1546_, v___x_1555_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object* v___f_1559_, lean_object* v_x_1560_){
_start:
{
lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_it_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_fst_1561_ = lean_ctor_get(v_x_1560_, 0);
v_snd_1562_ = lean_ctor_get(v_x_1560_, 1);
v___x_1563_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_box(0);
v___x_1566_ = l_String_splitOnAux(v_fst_1561_, v___x_1563_, v___x_1564_, v___x_1564_, v___x_1564_, v___x_1565_);
v_it_1567_ = l_List_mapTR_loop___redArg(v___f_1559_, v___x_1566_, v___x_1565_);
v___x_1568_ = l_String_intercalate(v___x_1563_, v_it_1567_);
v___x_1569_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1570_ = lean_string_append(v___x_1568_, v___x_1569_);
v___x_1571_ = lean_string_append(v___x_1570_, v_snd_1562_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1___boxed(lean_object* v___f_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Std_Http_Headers_instToString___lam__1(v___f_1572_, v_x_1573_);
lean_dec_ref(v_x_1573_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object* v___f_1576_, lean_object* v_headers_1577_){
_start:
{
lean_object* v_entries_1578_; lean_object* v___x_1579_; size_t v_sz_1580_; size_t v___x_1581_; lean_object* v_pairs_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v_entries_1578_ = lean_ctor_get(v_headers_1577_, 0);
lean_inc_ref(v_entries_1578_);
lean_dec_ref(v_headers_1577_);
v___x_1579_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_1580_ = lean_array_size(v_entries_1578_);
v___x_1581_ = ((size_t)0ULL);
v_pairs_1582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1579_, v___f_1576_, v_sz_1580_, v___x_1581_, v_entries_1578_);
v___x_1583_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1584_ = lean_array_to_list(v_pairs_1582_);
v___x_1585_ = l_String_intercalate(v___x_1583_, v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object* v___f_1592_, lean_object* v_buf_1593_, lean_object* v_name_1594_, lean_object* v_value_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v_data_1600_; lean_object* v_size_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1619_; 
v___x_1596_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = lean_box(0);
v___x_1599_ = l_String_splitOnAux(v_name_1594_, v___x_1596_, v___x_1597_, v___x_1597_, v___x_1597_, v___x_1598_);
v_data_1600_ = lean_ctor_get(v_buf_1593_, 0);
v_size_1601_ = lean_ctor_get(v_buf_1593_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_buf_1593_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1603_ = v_buf_1593_;
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_size_1601_);
lean_inc(v_data_1600_);
lean_dec(v_buf_1593_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_it_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v_it_1605_ = l_List_mapTR_loop___redArg(v___f_1592_, v___x_1599_, v___x_1598_);
v___x_1606_ = l_String_intercalate(v___x_1596_, v_it_1605_);
v___x_1607_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_1608_ = lean_string_append(v___x_1606_, v___x_1607_);
v___x_1609_ = lean_string_append(v___x_1608_, v_value_1595_);
v___x_1610_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_1611_ = lean_string_append(v___x_1609_, v___x_1610_);
v___x_1612_ = lean_string_to_utf8(v___x_1611_);
lean_dec_ref(v___x_1611_);
lean_inc_ref(v___x_1612_);
v___x_1613_ = lean_array_push(v_data_1600_, v___x_1612_);
v___x_1614_ = lean_byte_array_size(v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1615_ = lean_nat_add(v_size_1601_, v___x_1614_);
lean_dec(v_size_1601_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1615_);
lean_ctor_set(v___x_1603_, 0, v___x_1613_);
v___x_1617_ = v___x_1603_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object* v___f_1620_, lean_object* v_buf_1621_, lean_object* v_name_1622_, lean_object* v_value_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_Http_Headers_instEncodeV11___lam__1(v___f_1620_, v_buf_1621_, v_name_1622_, v_value_1623_);
lean_dec_ref(v_value_1623_);
lean_dec_ref(v_name_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object* v___f_1625_, lean_object* v_buffer_1626_, lean_object* v_headers_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Std_Http_Headers_fold___redArg(v_headers_1627_, v_buffer_1626_, v___f_1625_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object* v___f_1629_, lean_object* v_buffer_1630_, lean_object* v_headers_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_Http_Headers_instEncodeV11___lam__0(v___f_1629_, v_buffer_1630_, v_headers_1631_);
lean_dec_ref(v_headers_1631_);
return v_res_1632_;
}
}
static lean_object* _init_l_Std_Http_Headers_instEmptyCollection(void){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object* v_x_1639_){
_start:
{
lean_object* v_fst_1640_; lean_object* v___x_1641_; lean_object* v_entries_1642_; lean_object* v_indexes_1643_; lean_object* v___f_1644_; lean_object* v___f_1645_; lean_object* v_i_1646_; lean_object* v_f_1647_; lean_object* v_entries_1648_; lean_object* v_indexes_1649_; lean_object* v___x_1650_; 
v_fst_1640_ = lean_ctor_get(v_x_1639_, 0);
lean_inc(v_fst_1640_);
v___x_1641_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v_entries_1642_ = lean_ctor_get(v___x_1641_, 0);
v_indexes_1643_ = lean_ctor_get(v___x_1641_, 1);
v___f_1644_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1645_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1646_ = lean_array_get_size(v_entries_1642_);
v_f_1647_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1647_, 0, v_i_1646_);
lean_inc_ref(v_entries_1642_);
v_entries_1648_ = lean_array_push(v_entries_1642_, v_x_1639_);
lean_inc_ref(v_indexes_1643_);
v_indexes_1649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1644_, v___f_1645_, v_indexes_1643_, v_fst_1640_, v_f_1647_);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_entries_1648_);
lean_ctor_set(v___x_1650_, 1, v_indexes_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object* v_x_1653_, lean_object* v_s_1654_){
_start:
{
lean_object* v_fst_1655_; lean_object* v_entries_1656_; lean_object* v_indexes_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1670_; 
v_fst_1655_ = lean_ctor_get(v_x_1653_, 0);
lean_inc(v_fst_1655_);
v_entries_1656_ = lean_ctor_get(v_s_1654_, 0);
v_indexes_1657_ = lean_ctor_get(v_s_1654_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_s_1654_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1659_ = v_s_1654_;
v_isShared_1660_ = v_isSharedCheck_1670_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_indexes_1657_);
lean_inc(v_entries_1656_);
lean_dec(v_s_1654_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1670_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v_i_1663_; lean_object* v_f_1664_; lean_object* v_entries_1665_; lean_object* v_indexes_1666_; lean_object* v___x_1668_; 
v___f_1661_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1662_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_1663_ = lean_array_get_size(v_entries_1656_);
v_f_1664_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insert___lam__0), 2, 1);
lean_closure_set(v_f_1664_, 0, v_i_1663_);
v_entries_1665_ = lean_array_push(v_entries_1656_, v_x_1653_);
v_indexes_1666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1661_, v___f_1662_, v_indexes_1657_, v_fst_1655_, v_f_1664_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v_indexes_1666_);
lean_ctor_set(v___x_1659_, 0, v_entries_1665_);
v___x_1668_ = v___x_1659_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_entries_1665_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_indexes_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object* v_f_1675_, lean_object* v_a_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_apply_2(v_f_1675_, v_a_1676_, v___y_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object* v_inst_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_headers_1682_, lean_object* v_b_1683_, lean_object* v_f_1684_){
_start:
{
lean_object* v_entries_1685_; lean_object* v___f_1686_; size_t v_sz_1687_; size_t v___x_1688_; lean_object* v___x_1689_; 
v_entries_1685_ = lean_ctor_get(v_headers_1682_, 0);
lean_inc_ref(v_entries_1685_);
lean_dec_ref(v_headers_1682_);
v___f_1686_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1686_, 0, v_f_1684_);
v_sz_1687_ = lean_array_size(v_entries_1685_);
v___x_1688_ = ((size_t)0ULL);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1680_, v_entries_1685_, v___f_1686_, v_sz_1687_, v___x_1688_, v_b_1683_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object* v_inst_1690_){
_start:
{
lean_object* v___f_1691_; 
v___f_1691_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1691_, 0, v_inst_1690_);
return v___f_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object* v_m_1692_, lean_object* v_inst_1693_){
_start:
{
lean_object* v___f_1694_; 
v___f_1694_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1694_, 0, v_inst_1693_);
return v___f_1694_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Value(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instInhabitedHeaders_default = _init_l_Std_Http_instInhabitedHeaders_default();
lean_mark_persistent(l_Std_Http_instInhabitedHeaders_default);
l_Std_Http_instInhabitedHeaders = _init_l_Std_Http_instInhabitedHeaders();
lean_mark_persistent(l_Std_Http_instInhabitedHeaders);
l_Std_Http_instMembershipNameHeaders = _init_l_Std_Http_instMembershipNameHeaders();
lean_mark_persistent(l_Std_Http_instMembershipNameHeaders);
l_Std_Http_Headers_empty = _init_l_Std_Http_Headers_empty();
lean_mark_persistent(l_Std_Http_Headers_empty);
l_Std_Http_Headers_instEmptyCollection = _init_l_Std_Http_Headers_instEmptyCollection();
lean_mark_persistent(l_Std_Http_Headers_instEmptyCollection);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Data_Headers_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Headers_Name(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Headers_Value(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Headers(builtin);
}
#ifdef __cplusplus
}
#endif
